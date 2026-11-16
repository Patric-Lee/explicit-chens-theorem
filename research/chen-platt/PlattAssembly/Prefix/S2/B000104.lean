import PlattAssemblyKernel
import PlattCertificates.Count131072.C013328
import PlattCertificates.Count131072.C013329
import PlattCertificates.Count131072.C013330
import PlattCertificates.Count131072.C013331
import PlattCertificates.Count131072.C013332
import PlattCertificates.Count131072.C013333
import PlattCertificates.Count131072.C013334
import PlattCertificates.Count131072.C013335
import PlattCertificates.Count131072.C013336
import PlattCertificates.Count131072.C013337
import PlattCertificates.Count131072.C013338
import PlattCertificates.Count131072.C013339
import PlattCertificates.Count131072.C013340
import PlattCertificates.Count131072.C013341
import PlattCertificates.Count131072.C013342
import PlattCertificates.Count131072.C013343
import PlattCertificates.Count131072.C013344
import PlattCertificates.Count131072.C013345
import PlattCertificates.Count131072.C013346
import PlattCertificates.Count131072.C013347
import PlattCertificates.Count131072.C013348
import PlattCertificates.Count131072.C013349
import PlattCertificates.Count131072.C013350
import PlattCertificates.Count131072.C013351
import PlattCertificates.Count131072.C013352
import PlattCertificates.Count131072.C013353
import PlattCertificates.Count131072.C013354
import PlattCertificates.Count131072.C013355
import PlattCertificates.Count131072.C013356
import PlattCertificates.Count131072.C013357
import PlattCertificates.Count131072.C013358
import PlattCertificates.Count131072.C013359
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000104
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts13328 : List PrefixCut := [⟨4,31348905,31348927⟩,
⟨58,445629755,445630070⟩,
⟨112,859093776,859094388⟩,
⟨128,985123754,985124456⟩]
theorem checked13328 : checkPrefixCuts (2^48) 1750859777 9 Manual.Count131072.C013328.packed 128 cuts13328 = true := by
 decide +kernel
def pointBounds13328 : List (Nat × Nat × Nat) := [(1750863872,94713522447565,94713899409407),(1750919168,94713936728415,94714313690550),(1750974464,94714350192436,94714727154868)]
theorem point_links_checked13328 : (cuts13328.take 3).map (fun c => (1750859777-1+2*2^9*c.k,94713491098660+c.lower,94713868060480+c.upper)) = pointBounds13328 := by
 decide +kernel
def cuts13329 : List PrefixCut := [⟨38,301406237,301406449⟩,
⟨92,718219749,718220262⟩,
⟨128,992926882,992927593⟩]
theorem checked13329 : checkPrefixCuts (2^48) 1750990849 9 Manual.Count131072.C013329.packed 128 cuts13329 = true := by
 decide +kernel
def pointBounds13329 : List (Nat × Nat × Nat) := [(1751029760,94714777628651,94715154591385),(1751085056,94715194442163,94715571405198)]
theorem point_links_checked13329 : (cuts13329.take 2).map (fun c => (1750990849-1+2*2^9*c.k,94714476222414+c.lower,94714853184936+c.upper)) = pointBounds13329 := by
 decide +kernel
def cuts13330 : List PrefixCut := [⟨18,140485780,140485880⟩,
⟨72,560326925,560327324⟩,
⟨126,985458882,985459582⟩,
⟨128,1000245839,1000246550⟩]
theorem checked13330 : checkPrefixCuts (2^48) 1751121921 9 Manual.Count131072.C013330.packed 128 cuts13330 = true := by
 decide +kernel
def pointBounds13330 : List (Nat × Nat × Nat) := [(1751140352,94715609635076,94715986598409),(1751195648,94716029476221,94716406439853),(1751250944,94716454608178,94716831572111)]
theorem point_links_checked13330 : (cuts13330.take 3).map (fun c => (1751121921-1+2*2^9*c.k,94715469149296+c.lower,94715846112529+c.upper)) = pointBounds13330 := by
 decide +kernel
def cuts13331 : List PrefixCut := [⟨52,407277872,407278156⟩,
⟨106,823221954,823222537⟩,
⟨128,996153155,996153864⟩]
theorem checked13331 : checkPrefixCuts (2^48) 1751252993 9 Manual.Count131072.C013331.packed 128 cuts13331 = true := by
 decide +kernel
def pointBounds13331 : List (Nat × Nat × Nat) := [(1751306240,94716876673007,94717253637235),(1751361536,94717292617089,94717669581616)]
theorem point_links_checked13331 : (cuts13331.take 2).map (fun c => (1751252993-1+2*2^9*c.k,94716469395135+c.lower,94716846359079+c.upper)) = pointBounds13331 := by
 decide +kernel
def cuts13332 : List PrefixCut := [⟨32,252321211,252321394⟩,
⟨86,663417773,663418252⟩,
⟨128,986596826,986597538⟩]
theorem checked13332 : checkPrefixCuts (2^48) 1751384065 9 Manual.Count131072.C013332.packed 128 cuts13332 = true := by
 decide +kernel
def pointBounds13332 : List (Nat × Nat × Nat) := [(1751416832,94717717869501,94718094834337),(1751472128,94718128966063,94718505931195)]
theorem point_links_checked13332 : (cuts13332.take 2).map (fun c => (1751384065-1+2*2^9*c.k,94717465548290+c.lower,94717842512943+c.upper)) = pointBounds13332 := by
 decide +kernel
def cuts13333 : List PrefixCut := [⟨12,93207787,93207854⟩,
⟨66,514402499,514402867⟩,
⟨120,924656638,924657297⟩,
⟨128,986201672,986202376⟩]
theorem checked13333 : checkPrefixCuts (2^48) 1751515137 9 Manual.Count131072.C013333.packed 128 cuts13333 = true := by
 decide +kernel
def pointBounds13333 : List (Nat × Nat × Nat) := [(1751527424,94718545352903,94718922318335),(1751582720,94718966547615,94719343513348),(1751638016,94719376801754,94719753767778)]
theorem point_links_checked13333 : (cuts13333.take 3).map (fun c => (1751515137-1+2*2^9*c.k,94718452145116+c.lower,94718829110481+c.upper)) = pointBounds13333 := by
 decide +kernel
def cuts13334 : List PrefixCut := [⟨46,357855380,357855635⟩,
⟨100,776921334,776921884⟩,
⟨128,993519218,993519922⟩]
theorem checked13334 : checkPrefixCuts (2^48) 1751646209 9 Manual.Count131072.C013334.packed 128 cuts13334 = true := by
 decide +kernel
def pointBounds13334 : List (Nat × Nat × Nat) := [(1751693312,94719796202168,94720173168492),(1751748608,94720215268122,94720592234741)]
theorem point_links_checked13334 : (cuts13334.take 2).map (fun c => (1751646209-1+2*2^9*c.k,94719438346788+c.lower,94719815312857+c.upper)) = pointBounds13334 := by
 decide +kernel
def cuts13335 : List PrefixCut := [⟨26,197955766,197955909⟩,
⟨80,618601894,618602336⟩,
⟨128,985571754,985572457⟩]
theorem checked13335 : checkPrefixCuts (2^48) 1751777281 9 Manual.Count131072.C013335.packed 128 cuts13335 = true := by
 decide +kernel
def pointBounds13335 : List (Nat × Nat × Nat) := [(1751803904,94720629821772,94721006788688),(1751859200,94721050467900,94721427435115)]
theorem point_links_checked13335 : (cuts13335.take 2).map (fun c => (1751777281-1+2*2^9*c.k,94720431866006+c.lower,94720808832779+c.upper)) = pointBounds13335 := by
 decide +kernel
def cuts13336 : List PrefixCut := [⟨6,47075520,47075553⟩,
⟨60,465606394,465606729⟩,
⟨114,872074677,872075304⟩,
⟨128,974573333,974574033⟩]
theorem checked13336 : checkPrefixCuts (2^48) 1751908353 9 Manual.Count131072.C013336.packed 128 cuts13336 = true := by
 decide +kernel
def pointBounds13336 : List (Nat × Nat × Nat) := [(1751914496,94721464513280,94721841480789),(1751969792,94721883044154,94722260011965),(1752025088,94722289512437,94722666480540)]
theorem point_links_checked13336 : (cuts13336.take 3).map (fun c => (1751908353-1+2*2^9*c.k,94721417437760+c.lower,94721794405236+c.upper)) = pointBounds13336 := by
 decide +kernel
def cuts13337 : List PrefixCut := [⟨40,318897589,318897817⟩,
⟨94,742690446,742690975⟩,
⟨128,1006951689,1006952407⟩]
theorem checked13337 : checkPrefixCuts (2^48) 1752039425 9 Manual.Count131072.C013337.packed 128 cuts13337 = true := by
 decide +kernel
def pointBounds13337 : List (Nat × Nat × Nat) := [(1752080384,94722710908682,94723087877086),(1752135680,94723134701539,94723511670244)]
theorem point_links_checked13337 : (cuts13337.take 2).map (fun c => (1752039425-1+2*2^9*c.k,94722392011093+c.lower,94722768979269+c.upper)) = pointBounds13337 := by
 decide +kernel
def cuts13338 : List PrefixCut := [⟨20,158232975,158233088⟩,
⟨74,576537295,576537709⟩,
⟨128,991294411,991295121⟩]
theorem checked13338 : checkPrefixCuts (2^48) 1752170497 9 Manual.Count131072.C013338.packed 128 cuts13338 = true := by
 decide +kernel
def pointBounds13338 : List (Nat × Nat × Nat) := [(1752190976,94723557195757,94723934164764),(1752246272,94723975500077,94724352469385),(1752301568,94724390257193,94724767226797)]
theorem point_links_checked13338 : (cuts13338.take 3).map (fun c => (1752170497-1+2*2^9*c.k,94723398962782+c.lower,94723775931676+c.upper)) = pointBounds13338 := by
 decide +kernel
def cuts13339 : List PrefixCut := [⟨54,418117295,418117596⟩,
⟨108,835257646,835258250⟩,
⟨128,992344439,992345152⟩]
theorem checked13339 : checkPrefixCuts (2^48) 1752301569 9 Manual.Count131072.C013339.packed 128 cuts13339 = true := by
 decide +kernel
def pointBounds13339 : List (Nat × Nat × Nat) := [(1752356864,94724808374488,94725185344393),(1752412160,94725225514839,94725602485047)]
theorem point_links_checked13339 : (cuts13339.take 2).map (fun c => (1752301569-1+2*2^9*c.k,94724390257193+c.lower,94724767226797+c.upper)) = pointBounds13339 := by
 decide +kernel
def cuts13340 : List PrefixCut := [⟨34,251527642,251527822⟩,
⟨88,676030018,676030497⟩,
⟨128,985845528,985846227⟩]
theorem checked13340 : checkPrefixCuts (2^48) 1752432641 9 Manual.Count131072.C013340.packed 128 cuts13340 = true := by
 decide +kernel
def pointBounds13340 : List (Nat × Nat × Nat) := [(1752467456,94725634129274,94726011099771),(1752522752,94726058631650,94726435602446)]
theorem point_links_checked13340 : (cuts13340.take 2).map (fun c => (1752432641-1+2*2^9*c.k,94725382601632+c.lower,94725759571949+c.upper)) = pointBounds13340 := by
 decide +kernel
def cuts13341 : List PrefixCut := [⟨14,107606583,107606660⟩,
⟨68,519394317,519394689⟩,
⟨122,934059890,934060560⟩,
⟨128,984326367,984327072⟩]
theorem checked13341 : checkPrefixCuts (2^48) 1752563713 9 Manual.Count131072.C013341.packed 128 cuts13341 = true := by
 decide +kernel
def pointBounds13341 : List (Nat × Nat × Nat) := [(1752578048,94726476053743,94726853024836),(1752633344,94726887841477,94727264812865),(1752688640,94727302507050,94727679478736)]
theorem point_links_checked13341 : (cuts13341.take 3).map (fun c => (1752563713-1+2*2^9*c.k,94726368447160+c.lower,94726745418176+c.upper)) = pointBounds13341 := by
 decide +kernel
def cuts13342 : List PrefixCut := [⟨48,374824567,374824833⟩,
⟨102,799902221,799902790⟩,
⟨128,1003523616,1003524332⟩]
theorem checked13342 : checkPrefixCuts (2^48) 1752694785 9 Manual.Count131072.C013342.packed 128 cuts13342 = true := by
 decide +kernel
def pointBounds13342 : List (Nat × Nat × Nat) := [(1752743936,94727727598094,94728104570081),(1752799232,94728152675748,94728529648038)]
theorem point_links_checked13342 : (cuts13342.take 2).map (fun c => (1752694785-1+2*2^9*c.k,94727352773527+c.lower,94727729745248+c.upper)) = pointBounds13342 := by
 decide +kernel
def cuts13343 : List PrefixCut := [⟨28,210523249,210523398⟩,
⟨82,628347981,628348427⟩,
⟨128,972296676,972297370⟩]
theorem checked13343 : checkPrefixCuts (2^48) 1752825857 9 Manual.Count131072.C013343.packed 128 cuts13343 = true := by
 decide +kernel
def pointBounds13343 : List (Nat × Nat × Nat) := [(1752854528,94728566820392,94728943792978),(1752909824,94728984645124,94729361618007)]
theorem point_links_checked13343 : (cuts13343.take 2).map (fun c => (1752825857-1+2*2^9*c.k,94728356297143+c.lower,94728733269580+c.upper)) = pointBounds13343 := by
 decide +kernel
def cuts13344 : List PrefixCut := [⟨8,62783301,62783344⟩,
⟨62,474158968,474159307⟩,
⟨116,886163973,886164606⟩,
⟨128,977522634,977523331⟩]
theorem checked13344 : checkPrefixCuts (2^48) 1752956929 9 Manual.Count131072.C013344.packed 128 cuts13344 = true := by
 decide +kernel
def pointBounds13344 : List (Nat × Nat × Nat) := [(1752965120,94729391377120,94729768350294),(1753020416,94729802752787,94730179726257),(1753075712,94730214757792,94730591731556)]
theorem point_links_checked13344 : (cuts13344.take 3).map (fun c => (1752956929-1+2*2^9*c.k,94729328593819+c.lower,94729705566950+c.upper)) = pointBounds13344 := by
 decide +kernel
def cuts13345 : List PrefixCut := [⟨42,341826909,341827154⟩,
⟨96,751397704,751398242⟩,
⟨128,1002656834,1002657549⟩]
theorem checked13345 : checkPrefixCuts (2^48) 1753088001 9 Manual.Count131072.C013345.packed 128 cuts13345 = true := by
 decide +kernel
def pointBounds13345 : List (Nat × Nat × Nat) := [(1753131008,94730647943362,94731024917435),(1753186304,94731057514157,94731434488523)]
theorem point_links_checked13345 : (cuts13345.take 2).map (fun c => (1753088001-1+2*2^9*c.k,94730306116453+c.lower,94730683090281+c.upper)) = pointBounds13345 := by
 decide +kernel
def cuts13346 : List PrefixCut := [⟨22,164560075,164560196⟩,
⟨76,584540189,584540609⟩,
⟨128,988453645,988454350⟩]
theorem checked13346 : checkPrefixCuts (2^48) 1753219073 9 Manual.Count131072.C013346.packed 128 cuts13346 = true := by
 decide +kernel
def pointBounds13346 : List (Nat × Nat × Nat) := [(1753241600,94731473333362,94731850308026),(1753296896,94731893313476,94732270288439)]
theorem point_links_checked13346 : (cuts13346.take 2).map (fun c => (1753219073-1+2*2^9*c.k,94731308773287+c.lower,94731685747830+c.upper)) = pointBounds13346 := by
 decide +kernel
def cuts13347 : List PrefixCut := [⟨2,14127112,14127122⟩,
⟨56,433920261,433920571⟩,
⟨110,848402774,848403380⟩,
⟨128,982119519,982120223⟩]
theorem checked13347 : checkPrefixCuts (2^48) 1753350145 9 Manual.Count131072.C013347.packed 128 cuts13347 = true := by
 decide +kernel
def pointBounds13347 : List (Nat × Nat × Nat) := [(1753352192,94732311354044,94732688329302),(1753407488,94732731147193,94733108122751),(1753462784,94733145629706,94733522605560)]
theorem point_links_checked13347 : (cuts13347.take 3).map (fun c => (1753350145-1+2*2^9*c.k,94732297226932+c.lower,94732674202180+c.upper)) = pointBounds13347 := by
 decide +kernel
def cuts13348 : List PrefixCut := [⟨36,277381625,277381821⟩,
⟨90,701469014,701469514⟩,
⟨128,992961128,992961836⟩]
theorem checked13348 : checkPrefixCuts (2^48) 1753481217 9 Manual.Count131072.C013348.packed 128 cuts13348 = true := by
 decide +kernel
def pointBounds13348 : List (Nat × Nat × Nat) := [(1753518080,94733556728076,94733933704224),(1753573376,94733980815465,94734357791917)]
theorem point_links_checked13348 : (cuts13348.take 2).map (fun c => (1753481217-1+2*2^9*c.k,94733279346451+c.lower,94733656322403+c.upper)) = pointBounds13348 := by
 decide +kernel
def cuts13349 : List PrefixCut := [⟨16,126803452,126803543⟩,
⟨70,544283302,544283693⟩,
⟨124,961428966,961429655⟩,
⟨128,991763399,991764110⟩]
theorem checked13349 : checkPrefixCuts (2^48) 1753612289 9 Manual.Count131072.C013349.packed 128 cuts13349 = true := by
 decide +kernel
def pointBounds13349 : List (Nat × Nat × Nat) := [(1753628672,94734399111031,94734776087782),(1753683968,94734816590881,94735193567932),(1753739264,94735233736545,94735610713894)]
theorem point_links_checked13349 : (cuts13349.take 3).map (fun c => (1753612289-1+2*2^9*c.k,94734272307579+c.lower,94734649284239+c.upper)) = pointBounds13349 := by
 decide +kernel
def cuts13350 : List PrefixCut := [⟨50,375242208,375242475⟩,
⟨104,798941738,798942301⟩,
⟨128,986873870,986874565⟩]
theorem checked13350 : checkPrefixCuts (2^48) 1753743361 9 Manual.Count131072.C013350.packed 128 cuts13350 = true := by
 decide +kernel
def pointBounds13350 : List (Nat × Nat × Nat) := [(1753794560,94735639313186,94736016290824),(1753849856,94736063012716,94736439990650)]
theorem point_links_checked13350 : (cuts13350.take 2).map (fun c => (1753743361-1+2*2^9*c.k,94735264070978+c.lower,94735641048349+c.upper)) = pointBounds13350 := by
 decide +kernel
def cuts13351 : List PrefixCut := [⟨30,233988674,233988841⟩,
⟨84,648032606,648033070⟩,
⟨128,976851056,976851762⟩]
theorem checked13351 : checkPrefixCuts (2^48) 1753874433 9 Manual.Count131072.C013351.packed 128 cuts13351 = true := by
 decide +kernel
def pointBounds13351 : List (Nat × Nat × Nat) := [(1753905152,94736484933522,94736861911755),(1753960448,94736898977454,94737275955984)]
theorem point_links_checked13351 : (cuts13351.take 2).map (fun c => (1753874433-1+2*2^9*c.k,94736250944848+c.lower,94736627922914+c.upper)) = pointBounds13351 := by
 decide +kernel
def cuts13352 : List PrefixCut := [⟨10,71090431,71090483⟩,
⟨64,487033949,487034298⟩,
⟨118,914999333,914999991⟩,
⟨128,989615077,989615787⟩]
theorem checked13352 : checkPrefixCuts (2^48) 1754005505 9 Manual.Count131072.C013352.packed 128 cuts13352 = true := by
 decide +kernel
def pointBounds13352 : List (Nat × Nat × Nat) := [(1754015744,94737298886335,94737675865159),(1754071040,94737714829853,94738091808974),(1754126336,94738142795237,94738519774667)]
theorem point_links_checked13352 : (cuts13352.take 3).map (fun c => (1754005505-1+2*2^9*c.k,94737227795904+c.lower,94737604774676+c.upper)) = pointBounds13352 := by
 decide +kernel
def cuts13353 : List PrefixCut := [⟨44,345794321,345794565⟩,
⟨98,755922003,755922543⟩,
⟨128,983444246,983444949⟩]
theorem checked13353 : checkPrefixCuts (2^48) 1754136577 9 Manual.Count131072.C013353.packed 128 cuts13353 = true := by
 decide +kernel
def pointBounds13353 : List (Nat × Nat × Nat) := [(1754181632,94738563205302,94738940185028),(1754236928,94738973332984,94739350313006)]
theorem point_links_checked13353 : (cuts13353.take 2).map (fun c => (1754136577-1+2*2^9*c.k,94738217410981+c.lower,94738594390463+c.upper)) = pointBounds13353 := by
 decide +kernel
def cuts13354 : List PrefixCut := [⟨24,185641085,185641214⟩,
⟨78,599272722,599273145⟩,
⟨128,984333115,984333814⟩]
theorem checked13354 : checkPrefixCuts (2^48) 1754267649 9 Manual.Count131072.C013354.packed 128 cuts13354 = true := by
 decide +kernel
def pointBounds13354 : List (Nat × Nat × Nat) := [(1754292224,94739386496312,94739763476626),(1754347520,94739800127949,94740177108557)]
theorem point_links_checked13354 : (cuts13354.take 2).map (fun c => (1754267649-1+2*2^9*c.k,94739200855227+c.lower,94739577835412+c.upper)) = pointBounds13354 := by
 decide +kernel
def cuts13355 : List PrefixCut := [⟨4,33531819,33531843⟩,
⟨58,462539298,462539626⟩,
⟨112,878377809,878378439⟩,
⟨128,1005437001,1005437722⟩]
theorem checked13355 : checkPrefixCuts (2^48) 1754398721 9 Manual.Count131072.C013355.packed 128 cuts13355 = true := by
 decide +kernel
def pointBounds13355 : List (Nat × Nat × Nat) := [(1754402816,94740218720161,94740595701069),(1754458112,94740647727640,94741024708852),(1754513408,94741063566151,94741440547665)]
theorem point_links_checked13355 : (cuts13355.take 3).map (fun c => (1754398721-1+2*2^9*c.k,94740185188342+c.lower,94740562169226+c.upper)) = pointBounds13355 := by
 decide +kernel
def cuts13356 : List PrefixCut := [⟨38,292616613,292616817⟩,
⟨92,710674901,710675404⟩,
⟨128,997661347,997662045⟩]
theorem checked13356 : checkPrefixCuts (2^48) 1754529793 9 Manual.Count131072.C013356.packed 128 cuts13356 = true := by
 decide +kernel
def pointBounds13356 : List (Nat × Nat × Nat) := [(1754568704,94741483241956,94741860223765),(1754624000,94741901300244,94742278282352)]
theorem point_links_checked13356 : (cuts13356.take 2).map (fun c => (1754529793-1+2*2^9*c.k,94741190625343+c.lower,94741567606948+c.upper)) = pointBounds13356 := by
 decide +kernel
def cuts13357 : List PrefixCut := [⟨18,138758722,138758823⟩,
⟨72,548609620,548610020⟩,
⟨126,966628374,966629066⟩,
⟨128,980904299,980905002⟩]
theorem checked13357 : checkPrefixCuts (2^48) 1754660865 9 Manual.Count131072.C013357.packed 128 cuts13357 = true := by
 decide +kernel
def pointBounds13357 : List (Nat × Nat × Nat) := [(1754679296,94742327045412,94742704027816),(1754734592,94742736896310,94743113879013),(1754789888,94743154915064,94743531898059)]
theorem point_links_checked13357 : (cuts13357.take 3).map (fun c => (1754660865-1+2*2^9*c.k,94742188286690+c.lower,94742565268993+c.upper)) = pointBounds13357 := by
 decide +kernel
def cuts13358 : List PrefixCut := [⟨52,413032967,413033259⟩,
⟨106,822845115,822845704⟩,
⟨128,990294991,990295699⟩]
theorem checked13358 : checkPrefixCuts (2^48) 1754791937 9 Manual.Count131072.C013358.packed 128 cuts13358 = true := by
 decide +kernel
def pointBounds13358 : List (Nat × Nat × Nat) := [(1754845184,94743582223956,94743959207254),(1754900480,94743992036104,94744369019699)]
theorem point_links_checked13358 : (cuts13358.take 2).map (fun c => (1754791937-1+2*2^9*c.k,94743169190989+c.lower,94743546173995+c.upper)) = pointBounds13358 := by
 decide +kernel
def cuts13359 : List PrefixCut := [⟨32,246038418,246038595⟩,
⟨86,665608448,665608926⟩,
⟨128,992947220,992947935⟩]
theorem checked13359 : checkPrefixCuts (2^48) 1754923009 9 Manual.Count131072.C013359.packed 128 cuts13359 = true := by
 decide +kernel
def pointBounds13359 : List (Nat × Nat × Nat) := [(1754955776,94744405524398,94744782508289),(1755011072,94744825094428,94745202078620)]
theorem point_links_checked13359 : (cuts13359.take 2).map (fun c => (1754923009-1+2*2^9*c.k,94744159485980+c.lower,94744536469694+c.upper)) = pointBounds13359 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000104
