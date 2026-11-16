import PlattAssemblyKernel
import PlattCertificates.Count131072.C024032
import PlattCertificates.Count131072.C024033
import PlattCertificates.Count131072.C024034
import PlattCertificates.Count131072.C024035
import PlattCertificates.Count131072.C024036
import PlattCertificates.Count131072.C024037
import PlattCertificates.Count131072.C024038
import PlattCertificates.Count131072.C024039
import PlattCertificates.Count131072.C024040
import PlattCertificates.Count131072.C024041
import PlattCertificates.Count131072.C024042
import PlattCertificates.Count131072.C024043
import PlattCertificates.Count131072.C024044
import PlattCertificates.Count131072.C024045
import PlattCertificates.Count131072.C024046
import PlattCertificates.Count131072.C024047
import PlattCertificates.Count131072.C024048
import PlattCertificates.Count131072.C024049
import PlattCertificates.Count131072.C024050
import PlattCertificates.Count131072.C024051
import PlattCertificates.Count131072.C024052
import PlattCertificates.Count131072.C024053
import PlattCertificates.Count131072.C024054
import PlattCertificates.Count131072.C024055
import PlattCertificates.Count131072.C024056
import PlattCertificates.Count131072.C024057
import PlattCertificates.Count131072.C024058
import PlattCertificates.Count131072.C024059
import PlattCertificates.Count131072.C024060
import PlattCertificates.Count131072.C024061
import PlattCertificates.Count131072.C024062
import PlattCertificates.Count131072.C024063
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000126
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts24032 : List PrefixCut := [⟨48,201698674,201698785⟩,
⟨128,537171954,537172251⟩]
theorem checked24032 : checkPrefixCuts (2^48) 3153854465 9 Manual.Count131072.C024032.packed 128 cuts24032 = true := by
 decide +kernel
def pointBounds24032 : List (Nat × Nat × Nat) := [(3153903616,102391129106093,102391510837095)]
theorem point_links_checked24032 : (cuts24032.take 1).map (fun c => (3153854465-1+2*2^9*c.k,102390927407419+c.lower,102391309138310+c.upper)) = pointBounds24032 := by
 decide +kernel
def cuts24033 : List PrefixCut := [⟨17,70948938,70948977⟩,
⟨114,484140803,484141074⟩,
⟨128,541968769,541969070⟩]
theorem checked24033 : checkPrefixCuts (2^48) 3153985537 9 Manual.Count131072.C024033.packed 128 cuts24033 = true := by
 decide +kernel
def pointBounds24033 : List (Nat × Nat × Nat) := [(3154002944,102391535528311,102391917259538),(3154102272,102391948720176,102392330451635)]
theorem point_links_checked24033 : (cuts24033.take 2).map (fun c => (3153985537-1+2*2^9*c.k,102391464579373+c.lower,102391846310561+c.upper)) = pointBounds24033 := by
 decide +kernel
def cuts24034 : List PrefixCut := [⟨83,341251029,341251223⟩,
⟨128,529274288,529274590⟩]
theorem checked24034 : checkPrefixCuts (2^48) 3154116609 9 Manual.Count131072.C024034.packed 128 cuts24034 = true := by
 decide +kernel
def pointBounds24034 : List (Nat × Nat × Nat) := [(3154201600,102392347799171,102392729530854)]
theorem point_links_checked24034 : (cuts24034.take 1).map (fun c => (3154116609-1+2*2^9*c.k,102392006548142+c.lower,102392388279631+c.upper)) = pointBounds24034 := by
 decide +kernel
def cuts24035 : List PrefixCut := [⟨52,222197685,222197806⟩,
⟨128,543529957,543530263⟩]
theorem checked24035 : checkPrefixCuts (2^48) 3154247681 9 Manual.Count131072.C024035.packed 128 cuts24035 = true := by
 decide +kernel
def pointBounds24035 : List (Nat × Nat × Nat) := [(3154300928,102392758020115,102393139752027)]
theorem point_links_checked24035 : (cuts24035.take 1).map (fun c => (3154247681-1+2*2^9*c.k,102392535822430+c.lower,102392917554221+c.upper)) = pointBounds24035 := by
 decide +kernel
def cuts24036 : List PrefixCut := [⟨21,88429671,88429721⟩,
⟨118,499874051,499874331⟩,
⟨128,540473478,540473780⟩]
theorem checked24036 : checkPrefixCuts (2^48) 3154378753 9 Manual.Count131072.C024036.packed 128 cuts24036 = true := by
 decide +kernel
def pointBounds24036 : List (Nat × Nat × Nat) := [(3154400256,102393167782058,102393549514205),(3154499584,102393579226438,102393960958815)]
theorem point_links_checked24036 : (cuts24036.take 2).map (fun c => (3154378753-1+2*2^9*c.k,102393079352387+c.lower,102393461084484+c.upper)) = pointBounds24036 := by
 decide +kernel
def cuts24037 : List PrefixCut := [⟨87,369047439,369047642⟩,
⟨128,536078980,536079280⟩]
theorem checked24037 : checkPrefixCuts (2^48) 3154509825 9 Manual.Count131072.C024037.packed 128 cuts24037 = true := by
 decide +kernel
def pointBounds24037 : List (Nat × Nat × Nat) := [(3154598912,102393988873304,102394370605906)]
theorem point_links_checked24037 : (cuts24037.take 1).map (fun c => (3154509825-1+2*2^9*c.k,102393619825865+c.lower,102394001558264+c.upper)) = pointBounds24037 := by
 decide +kernel
def cuts24038 : List PrefixCut := [⟨56,235018248,235018375⟩,
⟨128,530703224,530703518⟩]
theorem checked24038 : checkPrefixCuts (2^48) 3154640897 9 Manual.Count131072.C024038.packed 128 cuts24038 = true := by
 decide +kernel
def pointBounds24038 : List (Nat × Nat × Nat) := [(3154698240,102394390923093,102394772655919)]
theorem point_links_checked24038 : (cuts24038.take 1).map (fun c => (3154640897-1+2*2^9*c.k,102394155904845+c.lower,102394537637544+c.upper)) = pointBounds24038 := by
 decide +kernel
def cuts24039 : List PrefixCut := [⟨25,104032365,104032423⟩,
⟨122,512123806,512124097⟩,
⟨128,537283374,537283680⟩]
theorem checked24039 : checkPrefixCuts (2^48) 3154771969 9 Manual.Count131072.C024039.packed 128 cuts24039 = true := by
 decide +kernel
def pointBounds24039 : List (Nat × Nat × Nat) := [(3154797568,102394790640434,102395172373485),(3154896896,102395198731875,102395580465159)]
theorem point_links_checked24039 : (cuts24039.take 2).map (fun c => (3154771969-1+2*2^9*c.k,102394686608069+c.lower,102395068341062+c.upper)) = pointBounds24039 := by
 decide +kernel
def cuts24040 : List PrefixCut := [⟨91,380867068,380867281⟩,
⟨128,536547369,536547670⟩]
theorem checked24040 : checkPrefixCuts (2^48) 3154903041 9 Manual.Count131072.C024040.packed 128 cuts24040 = true := by
 decide +kernel
def pointBounds24040 : List (Nat × Nat × Nat) := [(3154996224,102395604758511,102395986492023)]
theorem point_links_checked24040 : (cuts24040.take 1).map (fun c => (3154903041-1+2*2^9*c.k,102395223891443+c.lower,102395605624742+c.upper)) = pointBounds24040 := by
 decide +kernel
def cuts24041 : List PrefixCut := [⟨60,246051320,246051456⟩,
⟨128,524838229,524838530⟩]
theorem checked24041 : checkPrefixCuts (2^48) 3155034113 9 Manual.Count131072.C024041.packed 128 cuts24041 = true := by
 decide +kernel
def pointBounds24041 : List (Nat × Nat × Nat) := [(3155095552,102396006490132,102396388223868)]
theorem point_links_checked24041 : (cuts24041.take 1).map (fun c => (3155034113-1+2*2^9*c.k,102395760438812+c.lower,102396142172412+c.upper)) = pointBounds24041 := by
 decide +kernel
def cuts24042 : List PrefixCut := [⟨29,126054298,126054368⟩,
⟨126,533291498,533291799⟩,
⟨128,541230934,541231240⟩]
theorem checked24042 : checkPrefixCuts (2^48) 3155165185 9 Manual.Count131072.C024042.packed 128 cuts24042 = true := by
 decide +kernel
def pointBounds24042 : List (Nat × Nat × Nat) := [(3155194880,102396411331339,102396793065310),(3155294208,102396818568539,102397200302741)]
theorem point_links_checked24042 : (cuts24042.take 2).map (fun c => (3155165185-1+2*2^9*c.k,102396285277041+c.lower,102396667010942+c.upper)) = pointBounds24042 := by
 decide +kernel
def cuts24043 : List PrefixCut := [⟨95,400533838,400534066⟩,
⟨128,535856133,535856441⟩]
theorem checked24043 : checkPrefixCuts (2^48) 3155296257 9 Manual.Count131072.C024043.packed 128 cuts24043 = true := by
 decide +kernel
def pointBounds24043 : List (Nat × Nat × Nat) := [(3155393536,102397227041813,102397608776248)]
theorem point_links_checked24043 : (cuts24043.take 1).map (fun c => (3155296257-1+2*2^9*c.k,102396826507975+c.lower,102397208242182+c.upper)) = pointBounds24043 := by
 decide +kernel
def cuts24044 : List PrefixCut := [⟨64,264306951,264307100⟩,
⟨128,528162441,528162739⟩]
theorem checked24044 : checkPrefixCuts (2^48) 3155427329 9 Manual.Count131072.C024044.packed 128 cuts24044 = true := by
 decide +kernel
def pointBounds24044 : List (Nat × Nat × Nat) := [(3155492864,102397626671059,102398008405723)]
theorem point_links_checked24044 : (cuts24044.take 1).map (fun c => (3155427329-1+2*2^9*c.k,102397362364108+c.lower,102397744098623+c.upper)) = pointBounds24044 := by
 decide +kernel
def cuts24045 : List PrefixCut := [⟨33,132371660,132371736⟩,
⟨128,530281221,530281513⟩]
theorem checked24045 : checkPrefixCuts (2^48) 3155558401 9 Manual.Count131072.C024045.packed 128 cuts24045 = true := by
 decide +kernel
def pointBounds24045 : List (Nat × Nat × Nat) := [(3155592192,102398022898209,102398404633098)]
theorem point_links_checked24045 : (cuts24045.take 1).map (fun c => (3155558401-1+2*2^9*c.k,102397890526549+c.lower,102398272261362+c.upper)) = pointBounds24045 := by
 decide +kernel
def cuts24046 : List PrefixCut := [⟨2,7670855,7670859⟩,
⟨99,417698194,417698420⟩,
⟨128,537216431,537216725⟩]
theorem checked24046 : checkPrefixCuts (2^48) 3155689473 9 Manual.Count131072.C024046.packed 128 cuts24046 = true := by
 decide +kernel
def pointBounds24046 : List (Nat × Nat × Nat) := [(3155691520,102398428478625,102398810213734),(3155790848,102398838505964,102399220241295)]
theorem point_links_checked24046 : (cuts24046.take 2).map (fun c => (3155689473-1+2*2^9*c.k,102398420807770+c.lower,102398802542875+c.upper)) = pointBounds24046 := by
 decide +kernel
def cuts24047 : List PrefixCut := [⟨68,287820377,287820540⟩,
⟨128,542277924,542278223⟩]
theorem checked24047 : checkPrefixCuts (2^48) 3155820545 9 Manual.Count131072.C024047.packed 128 cuts24047 = true := by
 decide +kernel
def pointBounds24047 : List (Nat × Nat × Nat) := [(3155890176,102399245844578,102399627580140)]
theorem point_links_checked24047 : (cuts24047.take 1).map (fun c => (3155820545-1+2*2^9*c.k,102398958024201+c.lower,102399339759600+c.upper)) = pointBounds24047 := by
 decide +kernel
def cuts24048 : List PrefixCut := [⟨37,150371067,150371155⟩,
⟨128,526469301,526469601⟩]
theorem checked24048 : checkPrefixCuts (2^48) 3155951617 9 Manual.Count131072.C024048.packed 128 cuts24048 = true := by
 decide +kernel
def pointBounds24048 : List (Nat × Nat × Nat) := [(3155989504,102399650673192,102400032408978)]
theorem point_links_checked24048 : (cuts24048.take 1).map (fun c => (3155951617-1+2*2^9*c.k,102399500302125+c.lower,102399882037823+c.upper)) = pointBounds24048 := by
 decide +kernel
def cuts24049 : List PrefixCut := [⟨6,25685224,25685238⟩,
⟨103,432717873,432718111⟩,
⟨128,540270818,540271119⟩]
theorem checked24049 : checkPrefixCuts (2^48) 3156082689 9 Manual.Count131072.C024049.packed 128 cuts24049 = true := by
 decide +kernel
def pointBounds24049 : List (Nat × Nat × Nat) := [(3156088832,102400052456650,102400434192662),(3156188160,102400459489299,102400841225535)]
theorem point_links_checked24049 : (cuts24049.take 2).map (fun c => (3156082689-1+2*2^9*c.k,102400026771426+c.lower,102400408507424+c.upper)) = pointBounds24049 := by
 decide +kernel
def cuts24050 : List PrefixCut := [⟨72,303836791,303836956⟩,
⟨128,540872671,540872974⟩]
theorem checked24050 : checkPrefixCuts (2^48) 3156213761 9 Manual.Count131072.C024050.packed 128 cuts24050 = true := by
 decide +kernel
def pointBounds24050 : List (Nat × Nat × Nat) := [(3156287488,102400870879035,102401252615499)]
theorem point_links_checked24050 : (cuts24050.take 1).map (fun c => (3156213761-1+2*2^9*c.k,102400567042244+c.lower,102400948778543+c.upper)) = pointBounds24050 := by
 decide +kernel
def cuts24051 : List PrefixCut := [⟨41,168811862,168811954⟩,
⟨128,528722299,528722598⟩]
theorem checked24051 : checkPrefixCuts (2^48) 3156344833 9 Manual.Count131072.C024051.packed 128 cuts24051 = true := by
 decide +kernel
def pointBounds24051 : List (Nat × Nat × Nat) := [(3156386816,102401276726777,102401658463471)]
theorem point_links_checked24051 : (cuts24051.take 1).map (fun c => (3156344833-1+2*2^9*c.k,102401107914915+c.lower,102401489651517+c.upper)) = pointBounds24051 := by
 decide +kernel
def cuts24052 : List PrefixCut := [⟨10,42981696,42981718⟩,
⟨107,457810266,457810516⟩,
⟨128,546178116,546178415⟩]
theorem checked24052 : checkPrefixCuts (2^48) 3156475905 9 Manual.Count131072.C024052.packed 128 cuts24052 = true := by
 decide +kernel
def pointBounds24052 : List (Nat × Nat × Nat) := [(3156486144,102401679618910,102402061355833),(3156585472,102402094447480,102402476184631)]
theorem point_links_checked24052 : (cuts24052.take 2).map (fun c => (3156475905-1+2*2^9*c.k,102401636637214+c.lower,102402018374115+c.upper)) = pointBounds24052 := by
 decide +kernel
def cuts24053 : List PrefixCut := [⟨76,317352409,317352588⟩,
⟨128,533136845,533137150⟩]
theorem checked24053 : checkPrefixCuts (2^48) 3156606977 9 Manual.Count131072.C024053.packed 128 cuts24053 = true := by
 decide +kernel
def pointBounds24053 : List (Nat × Nat × Nat) := [(3156684800,102402500167739,102402881905118)]
theorem point_links_checked24053 : (cuts24053.take 1).map (fun c => (3156606977-1+2*2^9*c.k,102402182815330+c.lower,102402564552530+c.upper)) = pointBounds24053 := by
 decide +kernel
def cuts24054 : List PrefixCut := [⟨45,185643052,185643161⟩,
⟨128,530796420,530796721⟩]
theorem checked24054 : checkPrefixCuts (2^48) 3156738049 9 Manual.Count131072.C024054.packed 128 cuts24054 = true := by
 decide +kernel
def pointBounds24054 : List (Nat × Nat × Nat) := [(3156784128,102402901595227,102403283332841)]
theorem point_links_checked24054 : (cuts24054.take 1).map (fun c => (3156738049-1+2*2^9*c.k,102402715952175+c.lower,102403097689680+c.upper)) = pointBounds24054 := by
 decide +kernel
def cuts24055 : List PrefixCut := [⟨14,58312255,58312289⟩,
⟨111,461676054,461676319⟩,
⟨128,533627537,533627843⟩]
theorem checked24055 : checkPrefixCuts (2^48) 3156869121 9 Manual.Count131072.C024055.packed 128 cuts24055 = true := by
 decide +kernel
def pointBounds24055 : List (Nat × Nat × Nat) := [(3156883456,102403305060850,102403686798690),(3156982784,102403708424649,102404090162720)]
theorem point_links_checked24055 : (cuts24055.take 2).map (fun c => (3156869121-1+2*2^9*c.k,102403246748595+c.lower,102403628486401+c.upper)) = pointBounds24055 := by
 decide +kernel
def cuts24056 : List PrefixCut := [⟨80,332112825,332113011⟩,
⟨128,529058341,529058638⟩]
theorem checked24056 : checkPrefixCuts (2^48) 3157000193 9 Manual.Count131072.C024056.packed 128 cuts24056 = true := by
 decide +kernel
def pointBounds24056 : List (Nat × Nat × Nat) := [(3157082112,102404112488957,102404494227255)]
theorem point_links_checked24056 : (cuts24056.take 1).map (fun c => (3157000193-1+2*2^9*c.k,102403780376132+c.lower,102404162114244+c.upper)) = pointBounds24056 := by
 decide +kernel
def cuts24057 : List PrefixCut := [⟨49,202559151,202559267⟩,
⟨128,533226548,533226853⟩]
theorem checked24057 : checkPrefixCuts (2^48) 3157131265 9 Manual.Count131072.C024057.packed 128 cuts24057 = true := by
 decide +kernel
def pointBounds24057 : List (Nat × Nat × Nat) := [(3157181440,102404511993624,102404893732149)]
theorem point_links_checked24057 : (cuts24057.take 1).map (fun c => (3157131265-1+2*2^9*c.k,102404309434473+c.lower,102404691172882+c.upper)) = pointBounds24057 := by
 decide +kernel
def cuts24058 : List PrefixCut := [⟨18,75332856,75332897⟩,
⟨115,484618945,484619208⟩,
⟨128,538286078,538286370⟩]
theorem checked24058 : checkPrefixCuts (2^48) 3157262337 9 Manual.Count131072.C024058.packed 128 cuts24058 = true := by
 decide +kernel
def pointBounds24058 : List (Nat × Nat × Nat) := [(3157280768,102404917993877,102405299732632),(3157380096,102405327279966,102405709018943)]
theorem point_links_checked24058 : (cuts24058.take 2).map (fun c => (3157262337-1+2*2^9*c.k,102404842661021+c.lower,102405224399735+c.upper)) = pointBounds24058 := by
 decide +kernel
def cuts24059 : List PrefixCut := [⟨84,347047920,347048117⟩,
⟨128,533538873,533539179⟩]
theorem checked24059 : checkPrefixCuts (2^48) 3157393409 9 Manual.Count131072.C024059.packed 128 cuts24059 = true := by
 decide +kernel
def pointBounds24059 : List (Nat × Nat × Nat) := [(3157479424,102405727995019,102406109734222)]
theorem point_links_checked24059 : (cuts24059.take 1).map (fun c => (3157393409-1+2*2^9*c.k,102405380947099+c.lower,102405762686105+c.upper)) = pointBounds24059 := by
 decide +kernel
def cuts24060 : List PrefixCut := [⟨53,219560217,219560340⟩,
⟨128,534853882,534854183⟩]
theorem checked24060 : checkPrefixCuts (2^48) 3157524481 9 Manual.Count131072.C024060.packed 128 cuts24060 = true := by
 decide +kernel
def pointBounds24060 : List (Nat × Nat × Nat) := [(3157578752,102406134046189,102406515785624)]
theorem point_links_checked24060 : (cuts24060.take 1).map (fun c => (3157524481-1+2*2^9*c.k,102405914485972+c.lower,102406296225284+c.upper)) = pointBounds24060 := by
 decide +kernel
def cuts24061 : List PrefixCut := [⟨22,90477254,90477305⟩,
⟨119,490708823,490709098⟩,
⟨128,528770279,528770575⟩]
theorem checked24061 : checkPrefixCuts (2^48) 3157655553 9 Manual.Count131072.C024061.packed 128 cuts24061 = true := by
 decide +kernel
def pointBounds24061 : List (Nat × Nat × Nat) := [(3157678080,102406539817108,102406921556772),(3157777408,102406940048677,102407321788565)]
theorem point_links_checked24061 : (cuts24061.take 2).map (fun c => (3157655553-1+2*2^9*c.k,102406449339854+c.lower,102406831079467+c.upper)) = pointBounds24061 := by
 decide +kernel
def cuts24062 : List PrefixCut := [⟨88,366168640,366168841⟩,
⟨128,535879097,535879394⟩]
theorem checked24062 : checkPrefixCuts (2^48) 3157786625 9 Manual.Count131072.C024062.packed 128 cuts24062 = true := by
 decide +kernel
def pointBounds24062 : List (Nat × Nat × Nat) := [(3157876736,102407344278773,102407726018883)]
theorem point_links_checked24062 : (cuts24062.take 1).map (fun c => (3157786625-1+2*2^9*c.k,102406978110133+c.lower,102407359850042+c.upper)) = pointBounds24062 := by
 decide +kernel
def cuts24063 : List PrefixCut := [⟨57,238696160,238696295⟩,
⟨128,532469958,532470255⟩]
theorem checked24063 : checkPrefixCuts (2^48) 3157917697 9 Manual.Count131072.C024063.packed 128 cuts24063 = true := by
 decide +kernel
def pointBounds24063 : List (Nat × Nat × Nat) := [(3157976064,102407752685390,102408134425731)]
theorem point_links_checked24063 : (cuts24063.take 1).map (fun c => (3157917697-1+2*2^9*c.k,102407513989230+c.lower,102407895729436+c.upper)) = pointBounds24063 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000126
