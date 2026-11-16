import PlattAssemblyKernel
import PlattCertificates.Count131072.C025024
import PlattCertificates.Count131072.C025025
import PlattCertificates.Count131072.C025026
import PlattCertificates.Count131072.C025027
import PlattCertificates.Count131072.C025028
import PlattCertificates.Count131072.C025029
import PlattCertificates.Count131072.C025030
import PlattCertificates.Count131072.C025031
import PlattCertificates.Count131072.C025032
import PlattCertificates.Count131072.C025033
import PlattCertificates.Count131072.C025034
import PlattCertificates.Count131072.C025035
import PlattCertificates.Count131072.C025036
import PlattCertificates.Count131072.C025037
import PlattCertificates.Count131072.C025038
import PlattCertificates.Count131072.C025039
import PlattCertificates.Count131072.C025040
import PlattCertificates.Count131072.C025041
import PlattCertificates.Count131072.C025042
import PlattCertificates.Count131072.C025043
import PlattCertificates.Count131072.C025044
import PlattCertificates.Count131072.C025045
import PlattCertificates.Count131072.C025046
import PlattCertificates.Count131072.C025047
import PlattCertificates.Count131072.C025048
import PlattCertificates.Count131072.C025049
import PlattCertificates.Count131072.C025050
import PlattCertificates.Count131072.C025051
import PlattCertificates.Count131072.C025052
import PlattCertificates.Count131072.C025053
import PlattCertificates.Count131072.C025054
import PlattCertificates.Count131072.C025055
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000157
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts25024 : List PrefixCut := [⟨19,79799667,79799710⟩,
⟨120,486418957,486419223⟩,
⟨128,517960556,517960838⟩]
theorem checked25024 : checkPrefixCuts (2^48) 3283877889 9 Manual.Count131072.C025024.packed 128 cuts25024 = true := by
 decide +kernel
def pointBounds25024 : List (Nat × Nat × Nat) := [(3283897344,102910387040542,102910769063965),(3284000768,102910793659832,102911175683478)]
theorem point_links_checked25024 : (cuts25024.take 2).map (fun c => (3283877889-1+2*2^9*c.k,102910307240875+c.lower,102910689264255+c.upper)) = pointBounds25024 := by
 decide +kernel
def cuts25025 : List PrefixCut := [⟨93,365722478,365722685⟩,
⟨128,507997437,507997723⟩]
theorem checked25025 : checkPrefixCuts (2^48) 3284008961 9 Manual.Count131072.C025025.packed 128 cuts25025 = true := by
 decide +kernel
def pointBounds25025 : List (Nat × Nat × Nat) := [(3284104192,102911190923909,102911572947778)]
theorem point_links_checked25025 : (cuts25025.take 1).map (fun c => (3284008961-1+2*2^9*c.k,102910825201431+c.lower,102911207225093+c.upper)) = pointBounds25025 := by
 decide +kernel
def cuts25026 : List PrefixCut := [⟨66,265175848,265176002⟩,
⟨128,514405240,514405533⟩]
theorem checked25026 : checkPrefixCuts (2^48) 3284140033 9 Manual.Count131072.C025026.packed 128 cuts25026 = true := by
 decide +kernel
def pointBounds25026 : List (Nat × Nat × Nat) := [(3284207616,102911598374716,102911980398818)]
theorem point_links_checked25026 : (cuts25026.take 1).map (fun c => (3284140033-1+2*2^9*c.k,102911333198868+c.lower,102911715222816+c.upper)) = pointBounds25026 := by
 decide +kernel
def cuts25027 : List PrefixCut := [⟨39,157180030,157180116⟩,
⟨128,510956596,510956882⟩]
theorem checked25027 : checkPrefixCuts (2^48) 3284271105 9 Manual.Count131072.C025027.packed 128 cuts25027 = true := by
 decide +kernel
def pointBounds25027 : List (Nat × Nat × Nat) := [(3284311040,102912004784138,102912386808465)]
theorem point_links_checked25027 : (cuts25027.take 1).map (fun c => (3284271105-1+2*2^9*c.k,102911847604108+c.lower,102912229628349+c.upper)) = pointBounds25027 := by
 decide +kernel
def cuts25028 : List PrefixCut := [⟨12,49106296,49106323⟩,
⟨113,454890190,454890448⟩,
⟨128,517020716,517021007⟩]
theorem checked25028 : checkPrefixCuts (2^48) 3284402177 9 Manual.Count131072.C025028.packed 128 cuts25028 = true := by
 decide +kernel
def pointBounds25028 : List (Nat × Nat × Nat) := [(3284414464,102912407667000,102912789691554),(3284517888,102912813450894,102913195475679)]
theorem point_links_checked25028 : (cuts25028.take 2).map (fun c => (3284402177-1+2*2^9*c.k,102912358560704+c.lower,102912740585231+c.upper)) = pointBounds25028 := by
 decide +kernel
def cuts25029 : List PrefixCut := [⟨86,348182530,348182726⟩,
⟨128,515714737,515715027⟩]
theorem checked25029 : checkPrefixCuts (2^48) 3284533249 9 Manual.Count131072.C025029.packed 128 cuts25029 = true := by
 decide +kernel
def pointBounds25029 : List (Nat × Nat × Nat) := [(3284621312,102913223763950,102913605788964)]
theorem point_links_checked25029 : (cuts25029.take 1).map (fun c => (3284533249-1+2*2^9*c.k,102912875581420+c.lower,102913257606238+c.upper)) = pointBounds25029 := by
 decide +kernel
def cuts25030 : List PrefixCut := [⟨59,236769369,236769503⟩,
⟨128,518693269,518693557⟩]
theorem checked25030 : checkPrefixCuts (2^48) 3284664321 9 Manual.Count131072.C025030.packed 128 cuts25030 = true := by
 decide +kernel
def pointBounds25030 : List (Nat × Nat × Nat) := [(3284724736,102913628065526,102914010090768)]
theorem point_links_checked25030 : (cuts25030.take 1).map (fun c => (3284664321-1+2*2^9*c.k,102913391296157+c.lower,102913773321265+c.upper)) = pointBounds25030 := by
 decide +kernel
def cuts25031 : List PrefixCut := [⟨32,131019718,131019796⟩,
⟨128,511217819,511218112⟩]
theorem checked25031 : checkPrefixCuts (2^48) 3284795393 9 Manual.Count131072.C025031.packed 128 cuts25031 = true := by
 decide +kernel
def pointBounds25031 : List (Nat × Nat × Nat) := [(3284828160,102914041009144,102914423034618)]
theorem point_links_checked25031 : (cuts25031.take 1).map (fun c => (3284795393-1+2*2^9*c.k,102913909989426+c.lower,102914292014822+c.upper)) = pointBounds25031 := by
 decide +kernel
def cuts25032 : List PrefixCut := [⟨5,19793640,19793651⟩,
⟨106,427570134,427570370⟩,
⟨128,514282028,514282313⟩]
theorem checked25032 : checkPrefixCuts (2^48) 3284926465 9 Manual.Count131072.C025032.packed 128 cuts25032 = true := by
 decide +kernel
def pointBounds25032 : List (Nat × Nat × Nat) := [(3284931584,102914441000885,102914823026585),(3285035008,102914848777379,102915230803304)]
theorem point_links_checked25032 : (cuts25032.take 2).map (fun c => (3284926465-1+2*2^9*c.k,102914421207245+c.lower,102914803232934+c.upper)) = pointBounds25032 := by
 decide +kernel
def cuts25033 : List PrefixCut := [⟨79,315568095,315568278⟩,
⟨128,513061957,513062245⟩]
theorem checked25033 : checkPrefixCuts (2^48) 3285057537 9 Manual.Count131072.C025033.packed 128 cuts25033 = true := by
 decide +kernel
def pointBounds25033 : List (Nat × Nat × Nat) := [(3285138432,102915251057368,102915633083525)]
theorem point_links_checked25033 : (cuts25033.take 1).map (fun c => (3285057537-1+2*2^9*c.k,102914935489273+c.lower,102915317515247+c.upper)) = pointBounds25033 := by
 decide +kernel
def cuts25034 : List PrefixCut := [⟨52,210428318,210428437⟩,
⟨128,513641306,513641597⟩]
theorem checked25034 : checkPrefixCuts (2^48) 3285188609 9 Manual.Count131072.C025034.packed 128 cuts25034 = true := by
 decide +kernel
def pointBounds25034 : List (Nat × Nat × Nat) := [(3285241856,102915658979548,102916041005929)]
theorem point_links_checked25034 : (cuts25034.take 1).map (fun c => (3285188609-1+2*2^9*c.k,102915448551230+c.lower,102915830577492+c.upper)) = pointBounds25034 := by
 decide +kernel
def cuts25035 : List PrefixCut := [⟨25,98270626,98270682⟩,
⟨126,502654504,502654788⟩,
⟨128,510793455,510793743⟩]
theorem checked25035 : checkPrefixCuts (2^48) 3285319681 9 Manual.Count131072.C025035.packed 128 cuts25035 = true := by
 decide +kernel
def pointBounds25035 : List (Nat × Nat × Nat) := [(3285345280,102916060463162,102916442489771),(3285448704,102916464847040,102916846873877)]
theorem point_links_checked25035 : (cuts25035.take 2).map (fun c => (3285319681-1+2*2^9*c.k,102915962192536+c.lower,102916344219089+c.upper)) = pointBounds25035 := by
 decide +kernel
def cuts25036 : List PrefixCut := [⟨99,394861429,394861649⟩,
⟨128,516512989,516513274⟩]
theorem checked25036 : checkPrefixCuts (2^48) 3285450753 9 Manual.Count131072.C025036.packed 128 cuts25036 = true := by
 decide +kernel
def pointBounds25036 : List (Nat × Nat × Nat) := [(3285552128,102916867847420,102917249874481)]
theorem point_links_checked25036 : (cuts25036.take 1).map (fun c => (3285450753-1+2*2^9*c.k,102916472985991+c.lower,102916855012832+c.upper)) = pointBounds25036 := by
 decide +kernel
def cuts25037 : List PrefixCut := [⟨72,288960732,288960889⟩,
⟨128,508953734,508954013⟩]
theorem checked25037 : checkPrefixCuts (2^48) 3285581825 9 Manual.Count131072.C025037.packed 128 cuts25037 = true := by
 decide +kernel
def pointBounds25037 : List (Nat × Nat × Nat) := [(3285655552,102917278459712,102917660486995)]
theorem point_links_checked25037 : (cuts25037.take 1).map (fun c => (3285581825-1+2*2^9*c.k,102916989498980+c.lower,102917371526106+c.upper)) = pointBounds25037 := by
 decide +kernel
def cuts25038 : List PrefixCut := [⟨45,178270336,178270436⟩,
⟨128,514501525,514501817⟩]
theorem checked25038 : checkPrefixCuts (2^48) 3285712897 9 Manual.Count131072.C025038.packed 128 cuts25038 = true := by
 decide +kernel
def pointBounds25038 : List (Nat × Nat × Nat) := [(3285758976,102917676723050,102918058750555)]
theorem point_links_checked25038 : (cuts25038.take 1).map (fun c => (3285712897-1+2*2^9*c.k,102917498452714+c.lower,102917880480119+c.upper)) = pointBounds25038 := by
 decide +kernel
def cuts25039 : List PrefixCut := [⟨18,71699635,71699672⟩,
⟨119,478675334,478675599⟩,
⟨128,514909341,514909629⟩]
theorem checked25039 : checkPrefixCuts (2^48) 3285843969 9 Manual.Count131072.C025039.packed 128 cuts25039 = true := by
 decide +kernel
def pointBounds25039 : List (Nat × Nat × Nat) := [(3285862400,102918084653874,102918466681608),(3285965824,102918491629573,102918873657535)]
theorem point_links_checked25039 : (cuts25039.take 2).map (fun c => (3285843969-1+2*2^9*c.k,102918012954239+c.lower,102918394981936+c.upper)) = pointBounds25039 := by
 decide +kernel
def cuts25040 : List PrefixCut := [⟨92,368501819,368502025⟩,
⟨128,513604004,513604288⟩]
theorem checked25040 : checkPrefixCuts (2^48) 3285975041 9 Manual.Count131072.C025040.packed 128 cuts25040 = true := by
 decide +kernel
def pointBounds25040 : List (Nat × Nat × Nat) := [(3286069248,102918896365399,102919278393590)]
theorem point_links_checked25040 : (cuts25040.take 1).map (fun c => (3285975041-1+2*2^9*c.k,102918527863580+c.lower,102918909891565+c.upper)) = pointBounds25040 := by
 decide +kernel
def cuts25041 : List PrefixCut := [⟨65,260134798,260134941⟩,
⟨128,509814702,509814989⟩]
theorem checked25041 : checkPrefixCuts (2^48) 3286106113 9 Manual.Count131072.C025041.packed 128 cuts25041 = true := by
 decide +kernel
def pointBounds25041 : List (Nat × Nat × Nat) := [(3286172672,102919301602382,102919683630794)]
theorem point_links_checked25041 : (cuts25041.take 1).map (fun c => (3286106113-1+2*2^9*c.k,102919041467584+c.lower,102919423495853+c.upper)) = pointBounds25041 := by
 decide +kernel
def cuts25042 : List PrefixCut := [⟨38,148949061,148949145⟩,
⟨128,514933338,514933623⟩]
theorem checked25042 : checkPrefixCuts (2^48) 3286237185 9 Manual.Count131072.C025042.packed 128 cuts25042 = true := by
 decide +kernel
def pointBounds25042 : List (Nat × Nat × Nat) := [(3286276096,102919700231347,102920082259987)]
theorem point_links_checked25042 : (cuts25042.take 1).map (fun c => (3286237185-1+2*2^9*c.k,102919551282286+c.lower,102919933310842+c.upper)) = pointBounds25042 := by
 decide +kernel
def cuts25043 : List PrefixCut := [⟨11,41368508,41368532⟩,
⟨112,436632115,436632363⟩,
⟨128,499410652,499410933⟩]
theorem checked25043 : checkPrefixCuts (2^48) 3286368257 9 Manual.Count131072.C025043.packed 128 cuts25043 = true := by
 decide +kernel
def pointBounds25043 : List (Nat × Nat × Nat) := [(3286379520,102920107584132,102920489612997),(3286482944,102920502847739,102920884876828)]
theorem point_links_checked25043 : (cuts25043.take 2).map (fun c => (3286368257-1+2*2^9*c.k,102920066215624+c.lower,102920448244465+c.upper)) = pointBounds25043 := by
 decide +kernel
def cuts25044 : List PrefixCut := [⟨85,335641491,335641675⟩,
⟨128,508383347,508383628⟩]
theorem checked25044 : checkPrefixCuts (2^48) 3286499329 9 Manual.Count131072.C025044.packed 128 cuts25044 = true := by
 decide +kernel
def pointBounds25044 : List (Nat × Nat × Nat) := [(3286586368,102920901267767,102921283297073)]
theorem point_links_checked25044 : (cuts25044.take 1).map (fun c => (3286499329-1+2*2^9*c.k,102920565626276+c.lower,102920947655398+c.upper)) = pointBounds25044 := by
 decide +kernel
def cuts25045 : List PrefixCut := [⟨58,235000588,235000720⟩,
⟨128,514015418,514015706⟩]
theorem checked25045 : checkPrefixCuts (2^48) 3286630401 9 Manual.Count131072.C025045.packed 128 cuts25045 = true := by
 decide +kernel
def pointBounds25045 : List (Nat × Nat × Nat) := [(3286689792,102921309010211,102921691039746)]
theorem point_links_checked25045 : (cuts25045.take 1).map (fun c => (3286630401-1+2*2^9*c.k,102921074009623+c.lower,102921456039026+c.upper)) = pointBounds25045 := by
 decide +kernel
def cuts25046 : List PrefixCut := [⟨31,121092931,121092999⟩,
⟨128,511425715,511426005⟩]
theorem checked25046 : checkPrefixCuts (2^48) 3286761473 9 Manual.Count131072.C025046.packed 128 cuts25046 = true := by
 decide +kernel
def pointBounds25046 : List (Nat × Nat × Nat) := [(3286793216,102921709117972,102922091147731)]
theorem point_links_checked25046 : (cuts25046.take 1).map (fun c => (3286761473-1+2*2^9*c.k,102921588025041+c.lower,102921970054732+c.upper)) = pointBounds25046 := by
 decide +kernel
def cuts25047 : List PrefixCut := [⟨4,15842570,15842580⟩,
⟨105,425002291,425002531⟩,
⟨128,518170403,518170695⟩]
theorem checked25047 : checkPrefixCuts (2^48) 3286892545 9 Manual.Count131072.C025047.packed 128 cuts25047 = true := by
 decide +kernel
def pointBounds25047 : List (Nat × Nat × Nat) := [(3286896640,102922115293326,102922497323317),(3287000064,102922524453047,102922906483268)]
theorem point_links_checked25047 : (cuts25047.take 2).map (fun c => (3286892545-1+2*2^9*c.k,102922099450756+c.lower,102922481480737+c.upper)) = pointBounds25047 := by
 decide +kernel
def cuts25048 : List PrefixCut := [⟨78,314865588,314865762⟩,
⟨128,514296475,514296762⟩]
theorem checked25048 : checkPrefixCuts (2^48) 3287023617 9 Manual.Count131072.C025048.packed 128 cuts25048 = true := by
 decide +kernel
def pointBounds25048 : List (Nat × Nat × Nat) := [(3287103488,102922932486747,102923314517194)]
theorem point_links_checked25048 : (cuts25048.take 1).map (fun c => (3287023617-1+2*2^9*c.k,102922617621159+c.lower,102922999651432+c.upper)) = pointBounds25048 := by
 decide +kernel
def cuts25049 : List PrefixCut := [⟨51,205935493,205935607⟩,
⟨128,514704096,514704381⟩]
theorem checked25049 : checkPrefixCuts (2^48) 3287154689 9 Manual.Count131072.C025049.packed 128 cuts25049 = true := by
 decide +kernel
def pointBounds25049 : List (Nat × Nat × Nat) := [(3287206912,102923337853127,102923719883801)]
theorem point_links_checked25049 : (cuts25049.take 1).map (fun c => (3287154689-1+2*2^9*c.k,102923131917634+c.lower,102923513948194+c.upper)) = pointBounds25049 := by
 decide +kernel
def cuts25050 : List PrefixCut := [⟨24,97184375,97184426⟩,
⟨125,497730303,497730581⟩,
⟨128,509802998,509803282⟩]
theorem checked25050 : checkPrefixCuts (2^48) 3287285761 9 Manual.Count131072.C025050.packed 128 cuts25050 = true := by
 decide +kernel
def pointBounds25050 : List (Nat × Nat × Nat) := [(3287310336,102923743806105,102924125837001),(3287413760,102924144352033,102924526383156)]
theorem point_links_checked25050 : (cuts25050.take 2).map (fun c => (3287285761-1+2*2^9*c.k,102923646621730+c.lower,102924028652575+c.upper)) = pointBounds25050 := by
 decide +kernel
def cuts25051 : List PrefixCut := [⟨98,396765800,396766022⟩,
⟨128,514919866,514920155⟩]
theorem checked25051 : checkPrefixCuts (2^48) 3287416833 9 Manual.Count131072.C025051.packed 128 cuts25051 = true := by
 decide +kernel
def pointBounds25051 : List (Nat × Nat × Nat) := [(3287517184,102924553190528,102924935221879)]
theorem point_links_checked25051 : (cuts25051.take 1).map (fun c => (3287416833-1+2*2^9*c.k,102924156424728+c.lower,102924538455857+c.upper)) = pointBounds25051 := by
 decide +kernel
def cuts25052 : List PrefixCut := [⟨71,289472930,289473089⟩,
⟨128,515670001,515670289⟩]
theorem checked25052 : checkPrefixCuts (2^48) 3287547905 9 Manual.Count131072.C025052.packed 128 cuts25052 = true := by
 decide +kernel
def pointBounds25052 : List (Nat × Nat × Nat) := [(3287620608,102924960817524,102925342849101)]
theorem point_links_checked25052 : (cuts25052.take 1).map (fun c => (3287547905-1+2*2^9*c.k,102924671344594+c.lower,102925053376012+c.upper)) = pointBounds25052 := by
 decide +kernel
def cuts25053 : List PrefixCut := [⟨44,172941273,172941371⟩,
⟨128,510769334,510769625⟩]
theorem checked25053 : checkPrefixCuts (2^48) 3287678977 9 Manual.Count131072.C025053.packed 128 cuts25053 = true := by
 decide +kernel
def pointBounds25053 : List (Nat × Nat × Nat) := [(3287724032,102925359955868,102925741987672)]
theorem point_links_checked25053 : (cuts25053.take 1).map (fun c => (3287678977-1+2*2^9*c.k,102925187014595+c.lower,102925569046301+c.upper)) = pointBounds25053 := by
 decide +kernel
def cuts25054 : List PrefixCut := [⟨17,69430874,69430912⟩,
⟨118,464520372,464520637⟩,
⟨128,506554091,506554378⟩]
theorem checked25054 : checkPrefixCuts (2^48) 3287810049 9 Manual.Count131072.C025054.packed 128 cuts25054 = true := by
 decide +kernel
def pointBounds25054 : List (Nat × Nat × Nat) := [(3287827456,102925767214803,102926149246838),(3287930880,102926162304301,102926544336563)]
theorem point_links_checked25054 : (cuts25054.take 2).map (fun c => (3287810049-1+2*2^9*c.k,102925697783929+c.lower,102926079815926+c.upper)) = pointBounds25054 := by
 decide +kernel
def cuts25055 : List PrefixCut := [⟨91,362117745,362117954⟩,
⟨128,510728608,510728898⟩]
theorem checked25055 : checkPrefixCuts (2^48) 3287941121 9 Manual.Count131072.C025055.packed 128 cuts25055 = true := by
 decide +kernel
def pointBounds25055 : List (Nat × Nat × Nat) := [(3288034304,102926566455765,102926948488258)]
theorem point_links_checked25055 : (cuts25055.take 1).map (fun c => (3287941121-1+2*2^9*c.k,102926204338020+c.lower,102926586370304+c.upper)) = pointBounds25055 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000157
