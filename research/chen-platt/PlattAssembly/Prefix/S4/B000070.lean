import PlattAssemblyKernel
import PlattCertificates.Count131072.C032240
import PlattCertificates.Count131072.C032241
import PlattCertificates.Count131072.C032242
import PlattCertificates.Count131072.C032243
import PlattCertificates.Count131072.C032244
import PlattCertificates.Count131072.C032245
import PlattCertificates.Count131072.C032246
import PlattCertificates.Count131072.C032247
import PlattCertificates.Count131072.C032248
import PlattCertificates.Count131072.C032249
import PlattCertificates.Count131072.C032250
import PlattCertificates.Count131072.C032251
import PlattCertificates.Count131072.C032252
import PlattCertificates.Count131072.C032253
import PlattCertificates.Count131072.C032254
import PlattCertificates.Count131072.C032255
import PlattCertificates.Count131072.C032256
import PlattCertificates.Count131072.C032257
import PlattCertificates.Count131072.C032258
import PlattCertificates.Count131072.C032259
import PlattCertificates.Count131072.C032260
import PlattCertificates.Count131072.C032261
import PlattCertificates.Count131072.C032262
import PlattCertificates.Count131072.C032263
import PlattCertificates.Count131072.C032264
import PlattCertificates.Count131072.C032265
import PlattCertificates.Count131072.C032266
import PlattCertificates.Count131072.C032267
import PlattCertificates.Count131072.C032268
import PlattCertificates.Count131072.C032269
import PlattCertificates.Count131072.C032270
import PlattCertificates.Count131072.C032271
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000070
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts32240 : List PrefixCut := [⟨5,15239333,15239342⟩,
⟨128,390626935,390627159⟩]
theorem checked32240 : checkPrefixCuts (2^48) 4229693441 9 Manual.Count131072.C032240.packed 128 cuts32240 = true := by
 decide +kernel
def pointBounds32240 : List (Nat × Nat × Nat) := [(4229698560,106142975390746,106143359228096)]
theorem point_links_checked32240 : (cuts32240.take 1).map (fun c => (4229693441-1+2*2^9*c.k,106142960151413+c.lower,106143343988754+c.upper)) = pointBounds32240 := by
 decide +kernel
def cuts32241 : List PrefixCut := [⟨7,23024651,23024663⟩,
⟨128,398467049,398467269⟩]
theorem checked32241 : checkPrefixCuts (2^48) 4229824513 9 Manual.Count131072.C032241.packed 128 cuts32241 = true := by
 decide +kernel
def pointBounds32241 : List (Nat × Nat × Nat) := [(4229831680,106143373802999,106143757640576)]
theorem point_links_checked32241 : (cuts32241.take 1).map (fun c => (4229824513-1+2*2^9*c.k,106143350778348+c.lower,106143734615913+c.upper)) = pointBounds32241 := by
 decide +kernel
def cuts32242 : List PrefixCut := [⟨9,28014667,28014683⟩,
⟨128,395859540,395859764⟩]
theorem checked32242 : checkPrefixCuts (2^48) 4229955585 9 Manual.Count131072.C032242.packed 128 cuts32242 = true := by
 decide +kernel
def pointBounds32242 : List (Nat × Nat × Nat) := [(4229964800,106143777260064,106144161097865)]
theorem point_links_checked32242 : (cuts32242.take 1).map (fun c => (4229955585-1+2*2^9*c.k,106143749245397+c.lower,106144133083182+c.upper)) = pointBounds32242 := by
 decide +kernel
def cuts32243 : List PrefixCut := [⟨11,32937831,32937851⟩,
⟨128,392719884,392720102⟩]
theorem checked32243 : checkPrefixCuts (2^48) 4230086657 9 Manual.Count131072.C032243.packed 128 cuts32243 = true := by
 decide +kernel
def pointBounds32243 : List (Nat × Nat × Nat) := [(4230097920,106144178042768,106144561880797)]
theorem point_links_checked32243 : (cuts32243.take 1).map (fun c => (4230086657-1+2*2^9*c.k,106144145104937+c.lower,106144528942946+c.upper)) = pointBounds32243 := by
 decide +kernel
def cuts32244 : List PrefixCut := [⟨13,41653414,41653437⟩,
⟨128,396633424,396633648⟩]
theorem checked32244 : checkPrefixCuts (2^48) 4230217729 9 Manual.Count131072.C032244.packed 128 cuts32244 = true := by
 decide +kernel
def pointBounds32244 : List (Nat × Nat × Nat) := [(4230231040,106144579478235,106144963316485)]
theorem point_links_checked32244 : (cuts32244.take 1).map (fun c => (4230217729-1+2*2^9*c.k,106144537824821+c.lower,106144921663048+c.upper)) = pointBounds32244 := by
 decide +kernel
def cuts32245 : List PrefixCut := [⟨15,44978959,44978986⟩,
⟨128,388636862,388637087⟩]
theorem checked32245 : checkPrefixCuts (2^48) 4230348801 9 Manual.Count131072.C032245.packed 128 cuts32245 = true := by
 decide +kernel
def pointBounds32245 : List (Nat × Nat × Nat) := [(4230364160,106144979437204,106145363275682)]
theorem point_links_checked32245 : (cuts32245.take 1).map (fun c => (4230348801-1+2*2^9*c.k,106144934458245+c.lower,106145318296696+c.upper)) = pointBounds32245 := by
 decide +kernel
def cuts32246 : List PrefixCut := [⟨17,51963712,51963743⟩,
⟨128,396342717,396342938⟩]
theorem checked32246 : checkPrefixCuts (2^48) 4230479873 9 Manual.Count131072.C032246.packed 128 cuts32246 = true := by
 decide +kernel
def pointBounds32246 : List (Nat × Nat × Nat) := [(4230497280,106145375058819,106145758897526)]
theorem point_links_checked32246 : (cuts32246.take 1).map (fun c => (4230479873-1+2*2^9*c.k,106145323095107+c.lower,106145706933783+c.upper)) = pointBounds32246 := by
 decide +kernel
def cuts32247 : List PrefixCut := [⟨19,56353251,56353285⟩,
⟨128,393203411,393203640⟩]
theorem checked32247 : checkPrefixCuts (2^48) 4230610945 9 Manual.Count131072.C032247.packed 128 cuts32247 = true := by
 decide +kernel
def pointBounds32247 : List (Nat × Nat × Nat) := [(4230630400,106145775791075,106146159630006)]
theorem point_links_checked32247 : (cuts32247.take 1).map (fun c => (4230610945-1+2*2^9*c.k,106145719437824+c.lower,106146103276721+c.upper)) = pointBounds32247 := by
 decide +kernel
def cuts32248 : List PrefixCut := [⟨21,65931915,65931951⟩,
⟨128,395519861,395520081⟩]
theorem checked32248 : checkPrefixCuts (2^48) 4230742017 9 Manual.Count131072.C032248.packed 128 cuts32248 = true := by
 decide +kernel
def pointBounds32248 : List (Nat × Nat × Nat) := [(4230763520,106146178573150,106146562412312)]
theorem point_links_checked32248 : (cuts32248.take 1).map (fun c => (4230742017-1+2*2^9*c.k,106146112641235+c.lower,106146496480361+c.upper)) = pointBounds32248 := by
 decide +kernel
def cuts32249 : List PrefixCut := [⟨23,72316602,72316641⟩,
⟨128,396638579,396638801⟩]
theorem checked32249 : checkPrefixCuts (2^48) 4230873089 9 Manual.Count131072.C032249.packed 128 cuts32249 = true := by
 decide +kernel
def pointBounds32249 : List (Nat × Nat × Nat) := [(4230896640,106146580477698,106146964317083)]
theorem point_links_checked32249 : (cuts32249.take 1).map (fun c => (4230873089-1+2*2^9*c.k,106146508161096+c.lower,106146892000442+c.upper)) = pointBounds32249 := by
 decide +kernel
def cuts32250 : List PrefixCut := [⟨25,75507618,75507662⟩,
⟨128,390040196,390040422⟩]
theorem checked32250 : checkPrefixCuts (2^48) 4231004161 9 Manual.Count131072.C032250.packed 128 cuts32250 = true := by
 decide +kernel
def pointBounds32250 : List (Nat × Nat × Nat) := [(4231029760,106146980307293,106147364146905)]
theorem point_links_checked32250 : (cuts32250.take 1).map (fun c => (4231004161-1+2*2^9*c.k,106146904799675+c.lower,106147288639243+c.upper)) = pointBounds32250 := by
 decide +kernel
def cuts32251 : List PrefixCut := [⟨27,83887344,83887391⟩,
⟨128,392689055,392689270⟩]
theorem checked32251 : checkPrefixCuts (2^48) 4231135233 9 Manual.Count131072.C032251.packed 128 cuts32251 = true := by
 decide +kernel
def pointBounds32251 : List (Nat × Nat × Nat) := [(4231162880,106147378727215,106147762567056)]
theorem point_links_checked32251 : (cuts32251.take 1).map (fun c => (4231135233-1+2*2^9*c.k,106147294839871+c.lower,106147678679665+c.upper)) = pointBounds32251 := by
 decide +kernel
def cuts32252 : List PrefixCut := [⟨29,87809546,87809596⟩,
⟨128,390149109,390149331⟩]
theorem checked32252 : checkPrefixCuts (2^48) 4231266305 9 Manual.Count131072.C032252.packed 128 cuts32252 = true := by
 decide +kernel
def pointBounds32252 : List (Nat × Nat × Nat) := [(4231296000,106147775338472,106148159178531)]
theorem point_links_checked32252 : (cuts32252.take 1).map (fun c => (4231266305-1+2*2^9*c.k,106147687528926+c.lower,106148071368935+c.upper)) = pointBounds32252 := by
 decide +kernel
def cuts32253 : List PrefixCut := [⟨31,96853557,96853612⟩,
⟨128,395325521,395325744⟩]
theorem checked32253 : checkPrefixCuts (2^48) 4231397377 9 Manual.Count131072.C032253.packed 128 cuts32253 = true := by
 decide +kernel
def pointBounds32253 : List (Nat × Nat × Nat) := [(4231429120,106148174531592,106148558371878)]
theorem point_links_checked32253 : (cuts32253.take 1).map (fun c => (4231397377-1+2*2^9*c.k,106148077678035+c.lower,106148461518266+c.upper)) = pointBounds32253 := by
 decide +kernel
def cuts32254 : List PrefixCut := [⟨33,99710826,99710883⟩,
⟨128,392386492,392386710⟩]
theorem checked32254 : checkPrefixCuts (2^48) 4231528449 9 Manual.Count131072.C032254.packed 128 cuts32254 = true := by
 decide +kernel
def pointBounds32254 : List (Nat × Nat × Nat) := [(4231562240,106148572714382,106148956554893)]
theorem point_links_checked32254 : (cuts32254.take 1).map (fun c => (4231528449-1+2*2^9*c.k,106148473003556+c.lower,106148856844010+c.upper)) = pointBounds32254 := by
 decide +kernel
def cuts32255 : List PrefixCut := [⟨35,104363840,104363901⟩,
⟨128,388715994,388716221⟩]
theorem checked32255 : checkPrefixCuts (2^48) 4231659521 9 Manual.Count131072.C032255.packed 128 cuts32255 = true := by
 decide +kernel
def pointBounds32255 : List (Nat × Nat × Nat) := [(4231695360,106148969753888,106149353594621)]
theorem point_links_checked32255 : (cuts32255.take 1).map (fun c => (4231659521-1+2*2^9*c.k,106148865390048+c.lower,106149249230720+c.upper)) = pointBounds32255 := by
 decide +kernel
def cuts32256 : List PrefixCut := [⟨37,115135868,115135934⟩,
⟨128,394490640,394490868⟩]
theorem checked32256 : checkPrefixCuts (2^48) 4231790593 9 Manual.Count131072.C032256.packed 128 cuts32256 = true := by
 decide +kernel
def pointBounds32256 : List (Nat × Nat × Nat) := [(4231828480,106149369241910,106149753082875)]
theorem point_links_checked32256 : (cuts32256.take 1).map (fun c => (4231790593-1+2*2^9*c.k,106149254106042+c.lower,106149637946941+c.upper)) = pointBounds32256 := by
 decide +kernel
def cuts32257 : List PrefixCut := [⟨39,117859254,117859322⟩,
⟨128,390288168,390288391⟩]
theorem checked32257 : checkPrefixCuts (2^48) 4231921665 9 Manual.Count131072.C032257.packed 128 cuts32257 = true := by
 decide +kernel
def pointBounds32257 : List (Nat × Nat × Nat) := [(4231961600,106149766455936,106150150297131)]
theorem point_links_checked32257 : (cuts32257.take 1).map (fun c => (4231921665-1+2*2^9*c.k,106149648596682+c.lower,106150032437809+c.upper)) = pointBounds32257 := by
 decide +kernel
def cuts32258 : List PrefixCut := [⟨41,126501872,126501939⟩,
⟨128,394333169,394333392⟩]
theorem checked32258 : checkPrefixCuts (2^48) 4232052737 9 Manual.Count131072.C032258.packed 128 cuts32258 = true := by
 decide +kernel
def pointBounds32258 : List (Nat × Nat × Nat) := [(4232094720,106150165386722,106150549228139)]
theorem point_links_checked32258 : (cuts32258.take 1).map (fun c => (4232052737-1+2*2^9*c.k,106150038884850+c.lower,106150422726200+c.upper)) = pointBounds32258 := by
 decide +kernel
def cuts32259 : List PrefixCut := [⟨43,127296030,127296099⟩,
⟨128,389199887,389200100⟩]
theorem checked32259 : checkPrefixCuts (2^48) 4232183809 9 Manual.Count131072.C032259.packed 128 cuts32259 = true := by
 decide +kernel
def pointBounds32259 : List (Nat × Nat × Nat) := [(4232227840,106150560514049,106150944355691)]
theorem point_links_checked32259 : (cuts32259.take 1).map (fun c => (4232183809-1+2*2^9*c.k,106150433218019+c.lower,106150817059592+c.upper)) = pointBounds32259 := by
 decide +kernel
def cuts32260 : List PrefixCut := [⟨45,139529106,139529183⟩,
⟨128,390185465,390185683⟩]
theorem checked32260 : checkPrefixCuts (2^48) 4232314881 9 Manual.Count131072.C032260.packed 128 cuts32260 = true := by
 decide +kernel
def pointBounds32260 : List (Nat × Nat × Nat) := [(4232360960,106150961947012,106151345788875)]
theorem point_links_checked32260 : (cuts32260.take 1).map (fun c => (4232314881-1+2*2^9*c.k,106150822417906+c.lower,106151206259692+c.upper)) = pointBounds32260 := by
 decide +kernel
def cuts32261 : List PrefixCut := [⟨47,142118390,142118474⟩,
⟨128,392833430,392833654⟩]
theorem checked32261 : checkPrefixCuts (2^48) 4232445953 9 Manual.Count131072.C032261.packed 128 cuts32261 = true := by
 decide +kernel
def pointBounds32261 : List (Nat × Nat × Nat) := [(4232494080,106151354721761,106151738563849)]
theorem point_links_checked32261 : (cuts32261.take 1).map (fun c => (4232445953-1+2*2^9*c.k,106151212603371+c.lower,106151596445375+c.upper)) = pointBounds32261 := by
 decide +kernel
def cuts32262 : List PrefixCut := [⟨49,148897131,148897214⟩,
⟨128,387833755,387833975⟩]
theorem checked32262 : checkPrefixCuts (2^48) 4232577025 9 Manual.Count131072.C032262.packed 128 cuts32262 = true := by
 decide +kernel
def pointBounds32262 : List (Nat × Nat × Nat) := [(4232627200,106151754333932,106152138176243)]
theorem point_links_checked32262 : (cuts32262.take 1).map (fun c => (4232577025-1+2*2^9*c.k,106151605436801+c.lower,106151989279029+c.upper)) = pointBounds32262 := by
 decide +kernel
def cuts32263 : List PrefixCut := [⟨51,157603924,157604009⟩,
⟨128,399259533,399259758⟩]
theorem checked32263 : checkPrefixCuts (2^48) 4232708097 9 Manual.Count131072.C032263.packed 128 cuts32263 = true := by
 decide +kernel
def pointBounds32263 : List (Nat × Nat × Nat) := [(4232760320,106152150874480,106152534717013)]
theorem point_links_checked32263 : (cuts32263.take 1).map (fun c => (4232708097-1+2*2^9*c.k,106151993270556+c.lower,106152377113004+c.upper)) = pointBounds32263 := by
 decide +kernel
def cuts32264 : List PrefixCut := [⟨53,163849775,163849864⟩,
⟨128,395257379,395257598⟩]
theorem checked32264 : checkPrefixCuts (2^48) 4232839169 9 Manual.Count131072.C032264.packed 128 cuts32264 = true := by
 decide +kernel
def pointBounds32264 : List (Nat × Nat × Nat) := [(4232893440,106152556379864,106152940222626)]
theorem point_links_checked32264 : (cuts32264.take 1).map (fun c => (4232839169-1+2*2^9*c.k,106152392530089+c.lower,106152776372762+c.upper)) = pointBounds32264 := by
 decide +kernel
def cuts32265 : List PrefixCut := [⟨55,172289556,172289651⟩,
⟨128,396708025,396708248⟩]
theorem checked32265 : checkPrefixCuts (2^48) 4232970241 9 Manual.Count131072.C032265.packed 128 cuts32265 = true := by
 decide +kernel
def pointBounds32265 : List (Nat × Nat × Nat) := [(4233026560,106152960077024,106153343920011)]
theorem point_links_checked32265 : (cuts32265.take 1).map (fun c => (4232970241-1+2*2^9*c.k,106152787787468+c.lower,106153171630360+c.upper)) = pointBounds32265 := by
 decide +kernel
def cuts32266 : List PrefixCut := [⟨57,175608854,175608952⟩,
⟨128,393703577,393703798⟩]
theorem checked32266 : checkPrefixCuts (2^48) 4233101313 9 Manual.Count131072.C032266.packed 128 cuts32266 = true := by
 decide +kernel
def pointBounds32266 : List (Nat × Nat × Nat) := [(4233159680,106153360104347,106153743947560)]
theorem point_links_checked32266 : (cuts32266.take 1).map (fun c => (4233101313-1+2*2^9*c.k,106153184495493+c.lower,106153568338608+c.upper)) = pointBounds32266 := by
 decide +kernel
def cuts32267 : List PrefixCut := [⟨59,181055664,181055775⟩,
⟨128,389834929,389835163⟩]
theorem checked32267 : checkPrefixCuts (2^48) 4233232385 9 Manual.Count131072.C032267.packed 128 cuts32267 = true := by
 decide +kernel
def pointBounds32267 : List (Nat × Nat × Nat) := [(4233292800,106153759254734,106154143098181)]
theorem point_links_checked32267 : (cuts32267.take 1).map (fun c => (4233232385-1+2*2^9*c.k,106153578199070+c.lower,106153962042406+c.upper)) = pointBounds32267 := by
 decide +kernel
def cuts32268 : List PrefixCut := [⟨61,185704272,185704380⟩,
⟨128,391950498,391950726⟩]
theorem checked32268 : checkPrefixCuts (2^48) 4233363457 9 Manual.Count131072.C032268.packed 128 cuts32268 = true := by
 decide +kernel
def pointBounds32268 : List (Nat × Nat × Nat) := [(4233425920,106154153738271,106154537581949)]
theorem point_links_checked32268 : (cuts32268.take 1).map (fun c => (4233363457-1+2*2^9*c.k,106153968033999+c.lower,106154351877569+c.upper)) = pointBounds32268 := by
 decide +kernel
def cuts32269 : List PrefixCut := [⟨63,192945546,192945657⟩,
⟨128,393866434,393866657⟩]
theorem checked32269 : checkPrefixCuts (2^48) 4233494529 9 Manual.Count131072.C032269.packed 128 cuts32269 = true := by
 decide +kernel
def pointBounds32269 : List (Nat × Nat × Nat) := [(4233559040,106154552930043,106154936773952)]
theorem point_links_checked32269 : (cuts32269.take 1).map (fun c => (4233494529-1+2*2^9*c.k,106154359984497+c.lower,106154743828295+c.upper)) = pointBounds32269 := by
 decide +kernel
def cuts32270 : List PrefixCut := [⟨65,199588044,199588156⟩,
⟨128,391261401,391261622⟩]
theorem checked32270 : checkPrefixCuts (2^48) 4233625601 9 Manual.Count131072.C032270.packed 128 cuts32270 = true := by
 decide +kernel
def pointBounds32270 : List (Nat × Nat × Nat) := [(4233692160,106154953438975,106155337283108)]
theorem point_links_checked32270 : (cuts32270.take 1).map (fun c => (4233625601-1+2*2^9*c.k,106154753850931+c.lower,106155137694952+c.upper)) = pointBounds32270 := by
 decide +kernel
def cuts32271 : List PrefixCut := [⟨67,207094388,207094505⟩,
⟨128,394905806,394906027⟩]
theorem checked32271 : checkPrefixCuts (2^48) 4233756673 9 Manual.Count131072.C032271.packed 128 cuts32271 = true := by
 decide +kernel
def pointBounds32271 : List (Nat × Nat × Nat) := [(4233825280,106155352206720,106155736051079)]
theorem point_links_checked32271 : (cuts32271.take 1).map (fun c => (4233756673-1+2*2^9*c.k,106155145112332+c.lower,106155528956574+c.upper)) = pointBounds32271 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000070
