import PlattAssemblyKernel
import PlattCertificates.Count131072.C022048
import PlattCertificates.Count131072.C022049
import PlattCertificates.Count131072.C022050
import PlattCertificates.Count131072.C022051
import PlattCertificates.Count131072.C022052
import PlattCertificates.Count131072.C022053
import PlattCertificates.Count131072.C022054
import PlattCertificates.Count131072.C022055
import PlattCertificates.Count131072.C022056
import PlattCertificates.Count131072.C022057
import PlattCertificates.Count131072.C022058
import PlattCertificates.Count131072.C022059
import PlattCertificates.Count131072.C022060
import PlattCertificates.Count131072.C022061
import PlattCertificates.Count131072.C022062
import PlattCertificates.Count131072.C022063
import PlattCertificates.Count131072.C022064
import PlattCertificates.Count131072.C022065
import PlattCertificates.Count131072.C022066
import PlattCertificates.Count131072.C022067
import PlattCertificates.Count131072.C022068
import PlattCertificates.Count131072.C022069
import PlattCertificates.Count131072.C022070
import PlattCertificates.Count131072.C022071
import PlattCertificates.Count131072.C022072
import PlattCertificates.Count131072.C022073
import PlattCertificates.Count131072.C022074
import PlattCertificates.Count131072.C022075
import PlattCertificates.Count131072.C022076
import PlattCertificates.Count131072.C022077
import PlattCertificates.Count131072.C022078
import PlattCertificates.Count131072.C022079
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000064
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts22048 : List PrefixCut := [⟨42,189379382,189379490⟩,
⟨128,585540033,585540366⟩]
theorem checked22048 : checkPrefixCuts (2^48) 2893807617 9 Manual.Count131072.C022048.packed 128 cuts22048 = true := by
 decide +kernel
def pointBounds22048 : List (Nat × Nat × Nat) := [(2893850624,101281571546904,101281952647389)]
theorem point_links_checked22048 : (cuts22048.take 1).map (fun c => (2893807617-1+2*2^9*c.k,101281382167522+c.lower,101281763267899+c.upper)) = pointBounds22048 := by
 decide +kernel
def cuts22049 : List PrefixCut := [⟨3,14686795,14686804⟩,
⟨92,429509037,429509284⟩,
⟨128,598254814,598255154⟩]
theorem checked22049 : checkPrefixCuts (2^48) 2893938689 9 Manual.Count131072.C022049.packed 128 cuts22049 = true := by
 decide +kernel
def pointBounds22049 : List (Nat × Nat × Nat) := [(2893941760,101281982394350,101282363495069),(2894032896,101282397216592,101282778317549)]
theorem point_links_checked22049 : (cuts22049.take 2).map (fun c => (2893938689-1+2*2^9*c.k,101281967707555+c.lower,101282348808265+c.upper)) = pointBounds22049 := by
 decide +kernel
def cuts22050 : List PrefixCut := [⟨53,235851324,235851458⟩,
⟨128,576831165,576831495⟩]
theorem checked22050 : checkPrefixCuts (2^48) 2894069761 9 Manual.Count131072.C022050.packed 128 cuts22050 = true := by
 decide +kernel
def pointBounds22050 : List (Nat × Nat × Nat) := [(2894124032,101282801813693,101283182914877)]
theorem point_links_checked22050 : (cuts22050.take 1).map (fun c => (2894069761-1+2*2^9*c.k,101282565962369+c.lower,101282947063419+c.upper)) = pointBounds22050 := by
 decide +kernel
def cuts22051 : List PrefixCut := [⟨14,64674276,64674312⟩,
⟨103,470899141,470899404⟩,
⟨128,581084322,581084645⟩]
theorem checked22051 : checkPrefixCuts (2^48) 2894200833 9 Manual.Count131072.C022051.packed 128 cuts22051 = true := by
 decide +kernel
def pointBounds22051 : List (Nat × Nat × Nat) := [(2894215168,101283207467810,101283588569226),(2894306304,101283613692675,101283994794318)]
theorem point_links_checked22051 : (cuts22051.take 2).map (fun c => (2894200833-1+2*2^9*c.k,101283142793534+c.lower,101283523894914+c.upper)) = pointBounds22051 := by
 decide +kernel
def cuts22052 : List PrefixCut := [⟨64,293303834,293304000⟩,
⟨128,584850580,584850907⟩]
theorem checked22052 : checkPrefixCuts (2^48) 2894331905 9 Manual.Count131072.C022052.packed 128 cuts22052 = true := by
 decide +kernel
def pointBounds22052 : List (Nat × Nat × Nat) := [(2894397440,101284017181690,101284398283559)]
theorem point_links_checked22052 : (cuts22052.take 1).map (fun c => (2894331905-1+2*2^9*c.k,101283723877856+c.lower,101284104979559+c.upper)) = pointBounds22052 := by
 decide +kernel
def cuts22053 : List PrefixCut := [⟨25,112902081,112902146⟩,
⟨114,525701129,525701427⟩,
⟨128,585018647,585018978⟩]
theorem checked22053 : checkPrefixCuts (2^48) 2894462977 9 Manual.Count131072.C022053.packed 128 cuts22053 = true := by
 decide +kernel
def pointBounds22053 : List (Nat × Nat × Nat) := [(2894488576,101284421630517,101284802732612),(2894579712,101284834429565,101285215531893)]
theorem point_links_checked22053 : (cuts22053.take 2).map (fun c => (2894462977-1+2*2^9*c.k,101284308728436+c.lower,101284689830466+c.upper)) = pointBounds22053 := by
 decide +kernel
def cuts22054 : List PrefixCut := [⟨75,337423759,337423954⟩,
⟨128,574684683,574685011⟩]
theorem checked22054 : checkPrefixCuts (2^48) 2894594049 9 Manual.Count131072.C022054.packed 128 cuts22054 = true := by
 decide +kernel
def pointBounds22054 : List (Nat × Nat × Nat) := [(2894670848,101285231170842,101285612273398)]
theorem point_links_checked22054 : (cuts22054.take 1).map (fun c => (2894594049-1+2*2^9*c.k,101284893747083+c.lower,101285274849444+c.upper)) = pointBounds22054 := by
 decide +kernel
def cuts22055 : List PrefixCut := [⟨36,164329774,164329871⟩,
⟨125,569699991,569700328⟩,
⟨128,583701517,583701862⟩]
theorem checked22055 : checkPrefixCuts (2^48) 2894725121 9 Manual.Count131072.C022055.packed 128 cuts22055 = true := by
 decide +kernel
def pointBounds22055 : List (Nat × Nat × Nat) := [(2894761984,101285632761540,101286013864326),(2894853120,101286038131757,101286419234783)]
theorem point_links_checked22055 : (cuts22055.take 2).map (fun c => (2894725121-1+2*2^9*c.k,101285468431766+c.lower,101285849534455+c.upper)) = pointBounds22055 := by
 decide +kernel
def cuts22056 : List PrefixCut := [⟨86,395536933,395537158⟩,
⟨128,588633907,588634239⟩]
theorem checked22056 : checkPrefixCuts (2^48) 2894856193 9 Manual.Count131072.C022056.packed 128 cuts22056 = true := by
 decide +kernel
def pointBounds22056 : List (Nat × Nat × Nat) := [(2894944256,101286447670216,101286828773475)]
theorem point_links_checked22056 : (cuts22056.take 1).map (fun c => (2894856193-1+2*2^9*c.k,101286052133283+c.lower,101286433236317+c.upper)) = pointBounds22056 := by
 decide +kernel
def cuts22057 : List PrefixCut := [⟨47,215747965,215748091⟩,
⟨128,592107388,592107725⟩]
theorem checked22057 : checkPrefixCuts (2^48) 2894987265 9 Manual.Count131072.C022057.packed 128 cuts22057 = true := by
 decide +kernel
def pointBounds22057 : List (Nat × Nat × Nat) := [(2895035392,101286856515155,101287237618647)]
theorem point_links_checked22057 : (cuts22057.take 1).map (fun c => (2894987265-1+2*2^9*c.k,101286640767190+c.lower,101287021870556+c.upper)) = pointBounds22057 := by
 decide +kernel
def cuts22058 : List PrefixCut := [⟨8,39181205,39181225⟩,
⟨97,450722590,450722847⟩,
⟨128,590622319,590622659⟩]
theorem checked22058 : checkPrefixCuts (2^48) 2895118337 9 Manual.Count131072.C022058.packed 128 cuts22058 = true := by
 decide +kernel
def pointBounds22058 : List (Nat × Nat × Nat) := [(2895126528,101287272055783,101287653159506),(2895217664,101287683597168,101288064701128)]
theorem point_links_checked22058 : (cuts22058.take 2).map (fun c => (2895118337-1+2*2^9*c.k,101287232874578+c.lower,101287613978281+c.upper)) = pointBounds22058 := by
 decide +kernel
def cuts22059 : List PrefixCut := [⟨58,267253833,267253987⟩,
⟨128,587970665,587970998⟩]
theorem checked22059 : checkPrefixCuts (2^48) 2895249409 9 Manual.Count131072.C022059.packed 128 cuts22059 = true := by
 decide +kernel
def pointBounds22059 : List (Nat × Nat × Nat) := [(2895308800,101288090750730,101288471854927)]
theorem point_links_checked22059 : (cuts22059.take 1).map (fun c => (2895249409-1+2*2^9*c.k,101287823496897+c.lower,101288204600940+c.upper)) = pointBounds22059 := by
 decide +kernel
def cuts22060 : List PrefixCut := [⟨19,84868555,84868603⟩,
⟨108,499968065,499968352⟩,
⟨128,587652485,587652826⟩]
theorem checked22060 : checkPrefixCuts (2^48) 2895380481 9 Manual.Count131072.C022060.packed 128 cuts22060 = true := by
 decide +kernel
def pointBounds22060 : List (Nat × Nat × Nat) := [(2895399936,101288496336117,101288877440541),(2895491072,101288911435627,101289292540290)]
theorem point_links_checked22060 : (cuts22060.take 2).map (fun c => (2895380481-1+2*2^9*c.k,101288411467562+c.lower,101288792571938+c.upper)) = pointBounds22060 := by
 decide +kernel
def cuts22061 : List PrefixCut := [⟨69,310876268,310876447⟩,
⟨128,585778718,585779051⟩]
theorem checked22061 : checkPrefixCuts (2^48) 2895511553 9 Manual.Count131072.C022061.packed 128 cuts22061 = true := by
 decide +kernel
def pointBounds22061 : List (Nat × Nat × Nat) := [(2895582208,101289309996315,101289691101211)]
theorem point_links_checked22061 : (cuts22061.take 1).map (fun c => (2895511553-1+2*2^9*c.k,101288999120047+c.lower,101289380224764+c.upper)) = pointBounds22061 := by
 decide +kernel
def cuts22062 : List PrefixCut := [⟨30,134630092,134630167⟩,
⟨119,544052498,544052812⟩,
⟨128,585363400,585363738⟩]
theorem checked22062 : checkPrefixCuts (2^48) 2895642625 9 Manual.Count131072.C022062.packed 128 cuts22062 = true := by
 decide +kernel
def pointBounds22062 : List (Nat × Nat × Nat) := [(2895673344,101289719528857,101290100633982),(2895764480,101290128951263,101290510056627)]
theorem point_links_checked22062 : (cuts22062.take 2).map (fun c => (2895642625-1+2*2^9*c.k,101289584898765+c.lower,101289966003815+c.upper)) = pointBounds22062 := by
 decide +kernel
def cuts22063 : List PrefixCut := [⟨80,365960274,365960488⟩,
⟨128,588058606,588058950⟩]
theorem checked22063 : checkPrefixCuts (2^48) 2895773697 9 Manual.Count131072.C022063.packed 128 cuts22063 = true := by
 decide +kernel
def pointBounds22063 : List (Nat × Nat × Nat) := [(2895855616,101290536222439,101290917328041)]
theorem point_links_checked22063 : (cuts22063.take 1).map (fun c => (2895773697-1+2*2^9*c.k,101290170262165+c.lower,101290551367553+c.upper)) = pointBounds22063 := by
 decide +kernel
def cuts22064 : List PrefixCut := [⟨41,187201135,187201240⟩,
⟨128,578312371,578312702⟩]
theorem checked22064 : checkPrefixCuts (2^48) 2895904769 9 Manual.Count131072.C022064.packed 128 cuts22064 = true := by
 decide +kernel
def pointBounds22064 : List (Nat × Nat × Nat) := [(2895946752,101290945521906,101291326627743)]
theorem point_links_checked22064 : (cuts22064.take 1).map (fun c => (2895904769-1+2*2^9*c.k,101290758320771+c.lower,101291139426503+c.upper)) = pointBounds22064 := by
 decide +kernel
def cuts22065 : List PrefixCut := [⟨2,8941768,8941773⟩,
⟨91,418993009,418993247⟩,
⟨128,590143550,590143883⟩]
theorem checked22065 : checkPrefixCuts (2^48) 2896035841 9 Manual.Count131072.C022065.packed 128 cuts22065 = true := by
 decide +kernel
def pointBounds22065 : List (Nat × Nat × Nat) := [(2896037888,101291345574910,101291726680978),(2896129024,101291755626151,101292136732452)]
theorem point_links_checked22065 : (cuts22065.take 2).map (fun c => (2896035841-1+2*2^9*c.k,101291336633142+c.lower,101291717739205+c.upper)) = pointBounds22065 := by
 decide +kernel
def cuts22066 : List PrefixCut := [⟨52,237818700,237818837⟩,
⟨128,585063121,585063457⟩]
theorem checked22066 : checkPrefixCuts (2^48) 2896166913 9 Manual.Count131072.C022066.packed 128 cuts22066 = true := by
 decide +kernel
def pointBounds22066 : List (Nat × Nat × Nat) := [(2896220160,101292164595392,101292545701925)]
theorem point_links_checked22066 : (cuts22066.take 1).map (fun c => (2896166913-1+2*2^9*c.k,101291926776692+c.lower,101292307883088+c.upper)) = pointBounds22066 := by
 decide +kernel
def cuts22067 : List PrefixCut := [⟨13,58602042,58602076⟩,
⟨102,469489234,469489509⟩,
⟨128,586980362,586980703⟩]
theorem checked22067 : checkPrefixCuts (2^48) 2896297985 9 Manual.Count131072.C022067.packed 128 cuts22067 = true := by
 decide +kernel
def pointBounds22067 : List (Nat × Nat × Nat) := [(2896311296,101292570441855,101292951548621),(2896402432,101292981329047,101293362436054)]
theorem point_links_checked22067 : (cuts22067.take 2).map (fun c => (2896297985-1+2*2^9*c.k,101292511839813+c.lower,101292892946545+c.upper)) = pointBounds22067 := by
 decide +kernel
def cuts22068 : List PrefixCut := [⟨63,287552322,287552487⟩,
⟨128,578207780,578208113⟩]
theorem checked22068 : checkPrefixCuts (2^48) 2896429057 9 Manual.Count131072.C022068.packed 128 cuts22068 = true := by
 decide +kernel
def pointBounds22068 : List (Nat × Nat × Nat) := [(2896493568,101293386372497,101293767479735)]
theorem point_links_checked22068 : (cuts22068.take 1).map (fun c => (2896429057-1+2*2^9*c.k,101293098820175+c.lower,101293479927248+c.upper)) = pointBounds22068 := by
 decide +kernel
def cuts22069 : List PrefixCut := [⟨24,109224878,109224941⟩,
⟨113,515408966,515409258⟩,
⟨128,582943108,582943439⟩]
theorem checked22069 : checkPrefixCuts (2^48) 2896560129 9 Manual.Count131072.C022069.packed 128 cuts22069 = true := by
 decide +kernel
def pointBounds22069 : List (Nat × Nat × Nat) := [(2896584704,101293786252833,101294167360302),(2896675840,101294192436921,101294573544619)]
theorem point_links_checked22069 : (cuts22069.take 2).map (fun c => (2896560129-1+2*2^9*c.k,101293677027955+c.lower,101294058135361+c.upper)) = pointBounds22069 := by
 decide +kernel
def cuts22070 : List PrefixCut := [⟨74,338637169,338637365⟩,
⟨128,590398706,590399049⟩]
theorem checked22070 : checkPrefixCuts (2^48) 2896691201 9 Manual.Count131072.C022070.packed 128 cuts22070 = true := by
 decide +kernel
def pointBounds22070 : List (Nat × Nat × Nat) := [(2896766976,101294598608232,101294979716165)]
theorem point_links_checked22070 : (cuts22070.take 1).map (fun c => (2896691201-1+2*2^9*c.k,101294259971063+c.lower,101294641078800+c.upper)) = pointBounds22070 := by
 decide +kernel
def cuts22071 : List PrefixCut := [⟨35,154980050,154980138⟩,
⟨124,566469702,566470023⟩,
⟨128,581724207,581724538⟩]
theorem checked22071 : checkPrefixCuts (2^48) 2896822273 9 Manual.Count131072.C022071.packed 128 cuts22071 = true := by
 decide +kernel
def pointBounds22071 : List (Nat × Nat × Nat) := [(2896858112,101295005349819,101295386457987),(2896949248,101295416839471,101295797947872)]
theorem point_links_checked22071 : (cuts22071.take 2).map (fun c => (2896822273-1+2*2^9*c.k,101294850369769+c.lower,101295231477849+c.upper)) = pointBounds22071 := by
 decide +kernel
def cuts22072 : List PrefixCut := [⟨85,389032347,389032563⟩,
⟨128,582766870,582767199⟩]
theorem checked22072 : checkPrefixCuts (2^48) 2896953345 9 Manual.Count131072.C022072.packed 128 cuts22072 = true := by
 decide +kernel
def pointBounds22072 : List (Nat × Nat × Nat) := [(2897040384,101295821126323,101296202234950)]
theorem point_links_checked22072 : (cuts22072.take 1).map (fun c => (2896953345-1+2*2^9*c.k,101295432093976+c.lower,101295813202387+c.upper)) = pointBounds22072 := by
 decide +kernel
def cuts22073 : List PrefixCut := [⟨46,209373789,209373908⟩,
⟨128,578951447,578951779⟩]
theorem checked22073 : checkPrefixCuts (2^48) 2897084417 9 Manual.Count131072.C022073.packed 128 cuts22073 = true := by
 decide +kernel
def pointBounds22073 : List (Nat × Nat × Nat) := [(2897131520,101296224234635,101296605343494)]
theorem point_links_checked22073 : (cuts22073.take 1).map (fun c => (2897084417-1+2*2^9*c.k,101296014860846+c.lower,101296395969586+c.upper)) = pointBounds22073 := by
 decide +kernel
def cuts22074 : List PrefixCut := [⟨7,31769184,31769203⟩,
⟨96,439612534,439612788⟩,
⟨128,586600096,586600437⟩]
theorem checked22074 : checkPrefixCuts (2^48) 2897215489 9 Manual.Count131072.C022074.packed 128 cuts22074 = true := by
 decide +kernel
def pointBounds22074 : List (Nat × Nat × Nat) := [(2897222656,101296625581477,101297006690568),(2897313792,101297033424827,101297414534153)]
theorem point_links_checked22074 : (cuts22074.take 2).map (fun c => (2897215489-1+2*2^9*c.k,101296593812293+c.lower,101296974921365+c.upper)) = pointBounds22074 := by
 decide +kernel
def cuts22075 : List PrefixCut := [⟨57,263271687,263271837⟩,
⟨128,588516584,588516918⟩]
theorem checked22075 : checkPrefixCuts (2^48) 2897346561 9 Manual.Count131072.C022075.packed 128 cuts22075 = true := by
 decide +kernel
def pointBounds22075 : List (Nat × Nat × Nat) := [(2897404928,101297443684076,101297824793639)]
theorem point_links_checked22075 : (cuts22075.take 1).map (fun c => (2897346561-1+2*2^9*c.k,101297180412389+c.lower,101297561521802+c.upper)) = pointBounds22075 := by
 decide +kernel
def cuts22076 : List PrefixCut := [⟨18,79949914,79949958⟩,
⟨107,482411983,482412259⟩,
⟨128,579455613,579455946⟩]
theorem checked22076 : checkPrefixCuts (2^48) 2897477633 9 Manual.Count131072.C022076.packed 128 cuts22076 = true := by
 decide +kernel
def pointBounds22076 : List (Nat × Nat × Nat) := [(2897496064,101297848878887,101298229988678),(2897587200,101298251340956,101298632450979)]
theorem point_links_checked22076 : (cuts22076.take 2).map (fun c => (2897477633-1+2*2^9*c.k,101297768928973+c.lower,101298150038720+c.upper)) = pointBounds22076 := by
 decide +kernel
def cuts22077 : List PrefixCut := [⟨68,317062519,317062707⟩,
⟨128,590211920,590212265⟩]
theorem checked22077 : checkPrefixCuts (2^48) 2897608705 9 Manual.Count131072.C022077.packed 128 cuts22077 = true := by
 decide +kernel
def pointBounds22077 : List (Nat × Nat × Nat) := [(2897678336,101298665447105,101299046557373)]
theorem point_links_checked22077 : (cuts22077.take 1).map (fun c => (2897608705-1+2*2^9*c.k,101298348384586+c.lower,101298729494666+c.upper)) = pointBounds22077 := by
 decide +kernel
def cuts22078 : List PrefixCut := [⟨29,129384507,129384581⟩,
⟨118,538413662,538413966⟩,
⟨128,582317232,582317561⟩]
theorem checked22078 : checkPrefixCuts (2^48) 2897739777 9 Manual.Count131072.C022078.packed 128 cuts22078 = true := by
 decide +kernel
def pointBounds22078 : List (Nat × Nat × Nat) := [(2897769472,101299067981013,101299449091512),(2897860608,101299477010168,101299858120897)]
theorem point_links_checked22078 : (cuts22078.take 2).map (fun c => (2897739777-1+2*2^9*c.k,101298938596506+c.lower,101299319706931+c.upper)) = pointBounds22078 := by
 decide +kernel
def cuts22079 : List PrefixCut := [⟨79,354816838,354817034⟩,
⟨128,580639594,580639924⟩]
theorem checked22079 : checkPrefixCuts (2^48) 2897870849 9 Manual.Count131072.C022079.packed 128 cuts22079 = true := by
 decide +kernel
def pointBounds22079 : List (Nat × Nat × Nat) := [(2897951744,101299875730576,101300256841526)]
theorem point_links_checked22079 : (cuts22079.take 1).map (fun c => (2897870849-1+2*2^9*c.k,101299520913738+c.lower,101299902024492+c.upper)) = pointBounds22079 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000064
