import PlattAssemblyKernel
import PlattCertificates.Count131072.C045120
import PlattCertificates.Count131072.C045121
import PlattCertificates.Count131072.C045122
import PlattCertificates.Count131072.C045123
import PlattCertificates.Count131072.C045124
import PlattCertificates.Count131072.C045125
import PlattCertificates.Count131072.C045126
import PlattCertificates.Count131072.C045127
import PlattCertificates.Count131072.C045128
import PlattCertificates.Count131072.C045129
import PlattCertificates.Count131072.C045130
import PlattCertificates.Count131072.C045131
import PlattCertificates.Count131072.C045132
import PlattCertificates.Count131072.C045133
import PlattCertificates.Count131072.C045134
import PlattCertificates.Count131072.C045135
import PlattCertificates.Count131072.C045136
import PlattCertificates.Count131072.C045137
import PlattCertificates.Count131072.C045138
import PlattCertificates.Count131072.C045139
import PlattCertificates.Count131072.C045140
import PlattCertificates.Count131072.C045141
import PlattCertificates.Count131072.C045142
import PlattCertificates.Count131072.C045143
import PlattCertificates.Count131072.C045144
import PlattCertificates.Count131072.C045145
import PlattCertificates.Count131072.C045146
import PlattCertificates.Count131072.C045147
import PlattCertificates.Count131072.C045148
import PlattCertificates.Count131072.C045149
import PlattCertificates.Count131072.C045150
import PlattCertificates.Count131072.C045151
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000160
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts45120 : List PrefixCut := [⟨48,207945018,207945136⟩,
⟨64,275864093,275864251⟩]
theorem checked45120 : checkPrefixCuts (2^48) 5917900801 10 Manual.Count131072.C045120.packed 64 cuts45120 = true := by
 decide +kernel
def pointBounds45120 : List (Nat × Nat × Nat) := [(5917999104,110376093738032,110376480126729)]
theorem point_links_checked45120 : (cuts45120.take 1).map (fun c => (5917900801-1+2*2^10*c.k,110375885793014+c.lower,110376272181593+c.upper)) = pointBounds45120 := by
 decide +kernel
def cuts45121 : List PrefixCut := [⟨64,280138555,280138716⟩]
theorem checked45121 : checkPrefixCuts (2^48) 5918031873 10 Manual.Count131072.C045121.packed 64 cuts45121 = true := by
 decide +kernel
def cuts45122 : List PrefixCut := [⟨11,47656223,47656253⟩,
⟨64,279751843,279752003⟩]
theorem checked45122 : checkPrefixCuts (2^48) 5918162945 10 Manual.Count131072.C045122.packed 64 cuts45122 = true := by
 decide +kernel
def pointBounds45122 : List (Nat × Nat × Nat) := [(5918185472,110376489451885,110376875840813)]
theorem point_links_checked45122 : (cuts45122.take 1).map (fun c => (5918162945-1+2*2^10*c.k,110376441795662+c.lower,110376828184560+c.upper)) = pointBounds45122 := by
 decide +kernel
def cuts45123 : List PrefixCut := [⟨38,163938721,163938816⟩,
⟨64,278223720,278223879⟩]
theorem checked45123 : checkPrefixCuts (2^48) 5918294017 10 Manual.Count131072.C045123.packed 64 cuts45123 = true := by
 decide +kernel
def pointBounds45123 : List (Nat × Nat × Nat) := [(5918371840,110376885486226,110377271875379)]
theorem point_links_checked45123 : (cuts45123.take 1).map (fun c => (5918294017-1+2*2^10*c.k,110376721547505+c.lower,110377107936563+c.upper)) = pointBounds45123 := by
 decide +kernel
def cuts45124 : List PrefixCut := [⟨64,280310158,280310318⟩]
theorem checked45124 : checkPrefixCuts (2^48) 5918425089 10 Manual.Count131072.C045124.packed 64 cuts45124 = true := by
 decide +kernel
def cuts45125 : List PrefixCut := [⟨1,4993593,4993596⟩,
⟨64,277593149,277593313⟩]
theorem checked45125 : checkPrefixCuts (2^48) 5918556161 10 Manual.Count131072.C045125.packed 64 cuts45125 = true := by
 decide +kernel
def pointBounds45125 : List (Nat × Nat × Nat) := [(5918558208,110377285074976,110377671464356)]
theorem point_links_checked45125 : (cuts45125.take 1).map (fun c => (5918556161-1+2*2^10*c.k,110377280081383+c.lower,110377666470760+c.upper)) = pointBounds45125 := by
 decide +kernel
def cuts45126 : List PrefixCut := [⟨28,121555053,121555118⟩,
⟨64,277682144,277682296⟩]
theorem checked45126 : checkPrefixCuts (2^48) 5918687233 10 Manual.Count131072.C045126.packed 64 cuts45126 = true := by
 decide +kernel
def pointBounds45126 : List (Nat × Nat × Nat) := [(5918744576,110377679229585,110378065619191)]
theorem point_links_checked45126 : (cuts45126.take 1).map (fun c => (5918687233-1+2*2^10*c.k,110377557674532+c.lower,110377944064073+c.upper)) = pointBounds45126 := by
 decide +kernel
def cuts45127 : List PrefixCut := [⟨55,237920048,237920187⟩,
⟨64,276201782,276201944⟩]
theorem checked45127 : checkPrefixCuts (2^48) 5918818305 10 Manual.Count131072.C045127.packed 64 cuts45127 = true := by
 decide +kernel
def pointBounds45127 : List (Nat × Nat × Nat) := [(5918930944,110378073276724,110378459666556)]
theorem point_links_checked45127 : (cuts45127.take 1).map (fun c => (5918818305-1+2*2^10*c.k,110377835356676+c.lower,110378221746369+c.upper)) = pointBounds45127 := by
 decide +kernel
def cuts45128 : List PrefixCut := [⟨64,271250023,271250183⟩]
theorem checked45128 : checkPrefixCuts (2^48) 5918949377 10 Manual.Count131072.C045128.packed 64 cuts45128 = true := by
 decide +kernel
def cuts45129 : List PrefixCut := [⟨18,77227166,77227208⟩,
⟨64,274049644,274049797⟩]
theorem checked45129 : checkPrefixCuts (2^48) 5919080449 10 Manual.Count131072.C045129.packed 64 cuts45129 = true := by
 decide +kernel
def pointBounds45129 : List (Nat × Nat × Nat) := [(5919117312,110378460035647,110378846425704)]
theorem point_links_checked45129 : (cuts45129.take 1).map (fun c => (5919080449-1+2*2^10*c.k,110378382808481+c.lower,110378769198496+c.upper)) = pointBounds45129 := by
 decide +kernel
def cuts45130 : List PrefixCut := [⟨45,196248744,196248859⟩,
⟨64,277562443,277562607⟩]
theorem checked45130 : checkPrefixCuts (2^48) 5919211521 10 Manual.Count131072.C045130.packed 64 cuts45130 = true := by
 decide +kernel
def pointBounds45130 : List (Nat × Nat × Nat) := [(5919303680,110378853106869,110379239497152)]
theorem point_links_checked45130 : (cuts45130.take 1).map (fun c => (5919211521-1+2*2^10*c.k,110378656858125+c.lower,110379043248293+c.upper)) = pointBounds45130 := by
 decide +kernel
def cuts45131 : List PrefixCut := [⟨64,277366099,277366259⟩]
theorem checked45131 : checkPrefixCuts (2^48) 5919342593 10 Manual.Count131072.C045131.packed 64 cuts45131 = true := by
 decide +kernel
def cuts45132 : List PrefixCut := [⟨8,34188878,34188898⟩,
⟨64,275457911,275458073⟩]
theorem checked45132 : checkPrefixCuts (2^48) 5919473665 10 Manual.Count131072.C045132.packed 64 cuts45132 = true := by
 decide +kernel
def pointBounds45132 : List (Nat × Nat × Nat) := [(5919490048,110379245975545,110379632366057)]
theorem point_links_checked45132 : (cuts45132.take 1).map (fun c => (5919473665-1+2*2^10*c.k,110379211786667+c.lower,110379598177159+c.upper)) = pointBounds45132 := by
 decide +kernel
def cuts45133 : List PrefixCut := [⟨35,151254395,151254484⟩,
⟨64,278780261,278780423⟩]
theorem checked45133 : checkPrefixCuts (2^48) 5919604737 10 Manual.Count131072.C045133.packed 64 cuts45133 = true := by
 decide +kernel
def pointBounds45133 : List (Nat × Nat × Nat) := [(5919676416,110379638498973,110380024889716)]
theorem point_links_checked45133 : (cuts45133.take 1).map (fun c => (5919604737-1+2*2^10*c.k,110379487244578+c.lower,110379873635232+c.upper)) = pointBounds45133 := by
 decide +kernel
def cuts45134 : List PrefixCut := [⟨62,269074388,269074539⟩,
⟨64,278536344,278536501⟩]
theorem checked45134 : checkPrefixCuts (2^48) 5919735809 10 Manual.Count131072.C045134.packed 64 cuts45134 = true := by
 decide +kernel
def pointBounds45134 : List (Nat × Nat × Nat) := [(5919862784,110380035099227,110380421490194)]
theorem point_links_checked45134 : (cuts45134.take 1).map (fun c => (5919735809-1+2*2^10*c.k,110379766024839+c.lower,110380152415655+c.upper)) = pointBounds45134 := by
 decide +kernel
def cuts45135 : List PrefixCut := [⟨64,279005650,279005816⟩]
theorem checked45135 : checkPrefixCuts (2^48) 5919866881 10 Manual.Count131072.C045135.packed 64 cuts45135 = true := by
 decide +kernel
def cuts45136 : List PrefixCut := [⟨25,109308821,109308883⟩,
⟨64,278619127,278619289⟩]
theorem checked45136 : checkPrefixCuts (2^48) 5919997953 10 Manual.Count131072.C045136.packed 64 cuts45136 = true := by
 decide +kernel
def pointBounds45136 : List (Nat × Nat × Nat) := [(5920049152,110380432875654,110380819266855)]
theorem point_links_checked45136 : (cuts45136.take 1).map (fun c => (5919997953-1+2*2^10*c.k,110380323566833+c.lower,110380709957972+c.upper)) = pointBounds45136 := by
 decide +kernel
def cuts45137 : List PrefixCut := [⟨52,222177643,222177773⟩,
⟨64,272146857,272147015⟩]
theorem checked45137 : checkPrefixCuts (2^48) 5920129025 10 Manual.Count131072.C045137.packed 64 cuts45137 = true := by
 decide +kernel
def pointBounds45137 : List (Nat × Nat × Nat) := [(5920235520,110380824363603,110381210755034)]
theorem point_links_checked45137 : (cuts45137.take 1).map (fun c => (5920129025-1+2*2^10*c.k,110380602185960+c.lower,110380988577261+c.upper)) = pointBounds45137 := by
 decide +kernel
def cuts45138 : List PrefixCut := [⟨64,278416621,278416785⟩]
theorem checked45138 : checkPrefixCuts (2^48) 5920260097 10 Manual.Count131072.C045138.packed 64 cuts45138 = true := by
 decide +kernel
def cuts45139 : List PrefixCut := [⟨15,63422590,63422629⟩,
⟨64,274987375,274987538⟩]
theorem checked45139 : checkPrefixCuts (2^48) 5920391169 10 Manual.Count131072.C045139.packed 64 cuts45139 = true := by
 decide +kernel
def pointBounds45139 : List (Nat × Nat × Nat) := [(5920421888,110381216172028,110381602563690)]
theorem point_links_checked45139 : (cuts45139.take 1).map (fun c => (5920391169-1+2*2^10*c.k,110381152749438+c.lower,110381539141061+c.upper)) = pointBounds45139 := by
 decide +kernel
def cuts45140 : List PrefixCut := [⟨42,182370713,182370819⟩,
⟨64,278879689,278879853⟩]
theorem checked45140 : checkPrefixCuts (2^48) 5920522241 10 Manual.Count131072.C045140.packed 64 cuts45140 = true := by
 decide +kernel
def pointBounds45140 : List (Nat × Nat × Nat) := [(5920608256,110381610107526,110381996499418)]
theorem point_links_checked45140 : (cuts45140.take 1).map (fun c => (5920522241-1+2*2^10*c.k,110381427736813+c.lower,110381814128599+c.upper)) = pointBounds45140 := by
 decide +kernel
def cuts45141 : List PrefixCut := [⟨64,278255490,278255648⟩]
theorem checked45141 : checkPrefixCuts (2^48) 5920653313 10 Manual.Count131072.C045141.packed 64 cuts45141 = true := by
 decide +kernel
def cuts45142 : List PrefixCut := [⟨5,21915984,21915996⟩,
⟨64,276110028,276110191⟩]
theorem checked45142 : checkPrefixCuts (2^48) 5920784385 10 Manual.Count131072.C045142.packed 64 cuts45142 = true := by
 decide +kernel
def pointBounds45142 : List (Nat × Nat × Nat) := [(5920794624,110382006787976,110382393180096)]
theorem point_links_checked45142 : (cuts45142.take 1).map (fun c => (5920784385-1+2*2^10*c.k,110381984871992+c.lower,110382371264100+c.upper)) = pointBounds45142 := by
 decide +kernel
def cuts45143 : List PrefixCut := [⟨32,138195346,138195424⟩,
⟨64,274725317,274725475⟩]
theorem checked45143 : checkPrefixCuts (2^48) 5920915457 10 Manual.Count131072.C045143.packed 64 cuts45143 = true := by
 decide +kernel
def pointBounds45143 : List (Nat × Nat × Nat) := [(5920980992,110382399177366,110382785569715)]
theorem point_links_checked45143 : (cuts45143.take 1).map (fun c => (5920915457-1+2*2^10*c.k,110382260982020+c.lower,110382647374291+c.upper)) = pointBounds45143 := by
 decide +kernel
def cuts45144 : List PrefixCut := [⟨59,258461641,258461778⟩,
⟨64,280471282,280471430⟩]
theorem checked45144 : checkPrefixCuts (2^48) 5921046529 10 Manual.Count131072.C045144.packed 64 cuts45144 = true := by
 decide +kernel
def pointBounds45144 : List (Nat × Nat × Nat) := [(5921167360,110382794168978,110383180561544)]
theorem point_links_checked45144 : (cuts45144.take 1).map (fun c => (5921046529-1+2*2^10*c.k,110382535707337+c.lower,110382922099766+c.upper)) = pointBounds45144 := by
 decide +kernel
def cuts45145 : List PrefixCut := [⟨64,274570587,274570746⟩]
theorem checked45145 : checkPrefixCuts (2^48) 5921177601 10 Manual.Count131072.C045145.packed 64 cuts45145 = true := by
 decide +kernel
def cuts45146 : List PrefixCut := [⟨22,93074994,93075052⟩,
⟨64,275277476,275277640⟩]
theorem checked45146 : checkPrefixCuts (2^48) 5921308673 10 Manual.Count131072.C045146.packed 64 cuts45146 = true := by
 decide +kernel
def pointBounds45146 : List (Nat × Nat × Nat) := [(5921353728,110383183824200,110383570216994)]
theorem point_links_checked45146 : (cuts45146.take 1).map (fun c => (5921308673-1+2*2^10*c.k,110383090749206+c.lower,110383477141942+c.upper)) = pointBounds45146 := by
 decide +kernel
def cuts45147 : List PrefixCut := [⟨49,210672781,210672906⟩,
⟨64,275651685,275651846⟩]
theorem checked45147 : checkPrefixCuts (2^48) 5921439745 10 Manual.Count131072.C045147.packed 64 cuts45147 = true := by
 decide +kernel
def pointBounds45147 : List (Nat × Nat × Nat) := [(5921540096,110383576699463,110383963092488)]
theorem point_links_checked45147 : (cuts45147.take 1).map (fun c => (5921439745-1+2*2^10*c.k,110383366026682+c.lower,110383752419582+c.upper)) = pointBounds45147 := by
 decide +kernel
def cuts45148 : List PrefixCut := [⟨64,275217803,275217967⟩]
theorem checked45148 : checkPrefixCuts (2^48) 5921570817 10 Manual.Count131072.C045148.packed 64 cuts45148 = true := by
 decide +kernel
def cuts45149 : List PrefixCut := [⟨12,53949585,53949613⟩,
⟨64,281866236,281866399⟩]
theorem checked45149 : checkPrefixCuts (2^48) 5921701889 10 Manual.Count131072.C045149.packed 64 cuts45149 = true := by
 decide +kernel
def pointBounds45149 : List (Nat × Nat × Nat) := [(5921726464,110383970845755,110384357239008)]
theorem point_links_checked45149 : (cuts45149.take 1).map (fun c => (5921701889-1+2*2^10*c.k,110383916896170+c.lower,110384303289395+c.upper)) = pointBounds45149 := by
 decide +kernel
def cuts45150 : List PrefixCut := [⟨39,168451286,168451381⟩,
⟨64,277344512,277344672⟩]
theorem checked45150 : checkPrefixCuts (2^48) 5921832961 10 Manual.Count131072.C045150.packed 64 cuts45150 = true := by
 decide +kernel
def pointBounds45150 : List (Nat × Nat × Nat) := [(5921912832,110384367213692,110384753607175)]
theorem point_links_checked45150 : (cuts45150.take 1).map (fun c => (5921832961-1+2*2^10*c.k,110384198762406+c.lower,110384585155794+c.upper)) = pointBounds45150 := by
 decide +kernel
def cuts45151 : List PrefixCut := [⟨64,277813659,277813821⟩]
theorem checked45151 : checkPrefixCuts (2^48) 5921964033 10 Manual.Count131072.C045151.packed 64 cuts45151 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000160
