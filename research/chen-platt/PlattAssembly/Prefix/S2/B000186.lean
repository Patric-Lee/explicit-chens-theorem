import PlattAssemblyKernel
import PlattCertificates.Count131072.C015952
import PlattCertificates.Count131072.C015953
import PlattCertificates.Count131072.C015954
import PlattCertificates.Count131072.C015955
import PlattCertificates.Count131072.C015956
import PlattCertificates.Count131072.C015957
import PlattCertificates.Count131072.C015958
import PlattCertificates.Count131072.C015959
import PlattCertificates.Count131072.C015960
import PlattCertificates.Count131072.C015961
import PlattCertificates.Count131072.C015962
import PlattCertificates.Count131072.C015963
import PlattCertificates.Count131072.C015964
import PlattCertificates.Count131072.C015965
import PlattCertificates.Count131072.C015966
import PlattCertificates.Count131072.C015967
import PlattCertificates.Count131072.C015968
import PlattCertificates.Count131072.C015969
import PlattCertificates.Count131072.C015970
import PlattCertificates.Count131072.C015971
import PlattCertificates.Count131072.C015972
import PlattCertificates.Count131072.C015973
import PlattCertificates.Count131072.C015974
import PlattCertificates.Count131072.C015975
import PlattCertificates.Count131072.C015976
import PlattCertificates.Count131072.C015977
import PlattCertificates.Count131072.C015978
import PlattCertificates.Count131072.C015979
import PlattCertificates.Count131072.C015980
import PlattCertificates.Count131072.C015981
import PlattCertificates.Count131072.C015982
import PlattCertificates.Count131072.C015983
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000186
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts15952 : List PrefixCut := [⟨38,241861701,241861858⟩,
⟨102,658122152,658122574⟩,
⟨128,818952641,818953168⟩]
theorem checked15952 : checkPrefixCuts (2^48) 2094792705 9 Manual.Count131072.C015952.packed 128 cuts15952 = true := by
 decide +kernel
def pointBounds15952 : List (Nat × Nat × Nat) := [(2094831616,97075636773570,97076015336319),(2094897152,97076053034021,97076431597035)]
theorem point_links_checked15952 : (cuts15952.take 2).map (fun c => (2094792705-1+2*2^9*c.k,97075394911869+c.lower,97075773474461+c.upper)) = pointBounds15952 := by
 decide +kernel
def cuts15953 : List PrefixCut := [⟨38,247624026,247624189⟩,
⟨102,663992831,663993262⟩,
⟨128,828037729,828038263⟩]
theorem checked15953 : checkPrefixCuts (2^48) 2094923777 9 Manual.Count131072.C015953.packed 128 cuts15953 = true := by
 decide +kernel
def pointBounds15953 : List (Nat × Nat × Nat) := [(2094962688,97076461488536,97076840051818),(2095028224,97076877857341,97077256420891)]
theorem point_links_checked15953 : (cuts15953.take 2).map (fun c => (2094923777-1+2*2^9*c.k,97076213864510+c.lower,97076592427629+c.upper)) = pointBounds15953 := by
 decide +kernel
def cuts15954 : List PrefixCut := [⟨38,248414595,248414756⟩,
⟨102,664354321,664354752⟩,
⟨128,836315270,836315813⟩]
theorem checked15954 : checkPrefixCuts (2^48) 2095054849 9 Manual.Count131072.C015954.packed 128 cuts15954 = true := by
 decide +kernel
def pointBounds15954 : List (Nat × Nat × Nat) := [(2095093760,97077290316834,97077668880648),(2095159296,97077706256560,97078084820644)]
theorem point_links_checked15954 : (cuts15954.take 2).map (fun c => (2095054849-1+2*2^9*c.k,97077041902239+c.lower,97077420465892+c.upper)) = pointBounds15954 := by
 decide +kernel
def cuts15955 : List PrefixCut := [⟨38,236039504,236039658⟩,
⟨102,652893560,652893985⟩,
⟨128,820947984,820948518⟩]
theorem checked15955 : checkPrefixCuts (2^48) 2095185921 9 Manual.Count131072.C015955.packed 128 cuts15955 = true := by
 decide +kernel
def pointBounds15955 : List (Nat × Nat × Nat) := [(2095224832,97078114257013,97078492821363),(2095290368,97078531111069,97078909675690)]
theorem point_links_checked15955 : (cuts15955.take 2).map (fun c => (2095185921-1+2*2^9*c.k,97077878217509+c.lower,97078256781705+c.upper)) = pointBounds15955 := by
 decide +kernel
def cuts15956 : List PrefixCut := [⟨38,240323529,240323684⟩,
⟨102,658897742,658898164⟩,
⟨128,826672991,826673521⟩]
theorem checked15956 : checkPrefixCuts (2^48) 2095316993 9 Manual.Count131072.C015956.packed 128 cuts15956 = true := by
 decide +kernel
def pointBounds15956 : List (Nat × Nat × Nat) := [(2095355904,97078939489022,97079318053907),(2095421440,97079358063235,97079736628387)]
theorem point_links_checked15956 : (cuts15956.take 2).map (fun c => (2095316993-1+2*2^9*c.k,97078699165493+c.lower,97079077730223+c.upper)) = pointBounds15956 := by
 decide +kernel
def cuts15957 : List PrefixCut := [⟨38,242054695,242054850⟩,
⟨102,651871780,651872202⟩,
⟨128,822591576,822592105⟩]
theorem checked15957 : checkPrefixCuts (2^48) 2095448065 9 Manual.Count131072.C015957.packed 128 cuts15957 = true := by
 decide +kernel
def pointBounds15957 : List (Nat × Nat × Nat) := [(2095486976,97079767893179,97080146458594),(2095552512,97080177710264,97080556275946)]
theorem point_links_checked15957 : (cuts15957.take 2).map (fun c => (2095448065-1+2*2^9*c.k,97079525838484+c.lower,97079904403744+c.upper)) = pointBounds15957 := by
 decide +kernel
def cuts15958 : List PrefixCut := [⟨38,241636589,241636747⟩,
⟨102,653442776,653443202⟩,
⟨128,818645157,818645688⟩]
theorem checked15958 : checkPrefixCuts (2^48) 2095579137 9 Manual.Count131072.C015958.packed 128 cuts15958 = true := by
 decide +kernel
def pointBounds15958 : List (Nat × Nat × Nat) := [(2095618048,97080590066649,97080968632596),(2095683584,97081001872836,97081380439051)]
theorem point_links_checked15958 : (cuts15958.take 2).map (fun c => (2095579137-1+2*2^9*c.k,97080348430060+c.lower,97080726995849+c.upper)) = pointBounds15958 := by
 decide +kernel
def cuts15959 : List PrefixCut := [⟨38,246053676,246053836⟩,
⟨102,659445800,659446224⟩,
⟨128,822891942,822892472⟩]
theorem checked15959 : checkPrefixCuts (2^48) 2095710209 9 Manual.Count131072.C015959.packed 128 cuts15959 = true := by
 decide +kernel
def pointBounds15959 : List (Nat × Nat × Nat) := [(2095749120,97081413128893,97081791695373),(2095814656,97081826521017,97082205087761)]
theorem point_links_checked15959 : (cuts15959.take 2).map (fun c => (2095710209-1+2*2^9*c.k,97081167075217+c.lower,97081545641537+c.upper)) = pointBounds15959 := by
 decide +kernel
def cuts15960 : List PrefixCut := [⟨38,240129092,240129246⟩,
⟨102,648257807,648258227⟩,
⟨128,816931142,816931672⟩]
theorem checked15960 : checkPrefixCuts (2^48) 2095841281 9 Manual.Count131072.C015960.packed 128 cuts15960 = true := by
 decide +kernel
def pointBounds15960 : List (Nat × Nat × Nat) := [(2095880192,97082230096251,97082608663255),(2095945728,97082638224966,97083016792236)]
theorem point_links_checked15960 : (cuts15960.take 2).map (fun c => (2095841281-1+2*2^9*c.k,97081989967159+c.lower,97082368534009+c.upper)) = pointBounds15960 := by
 decide +kernel
def cuts15961 : List PrefixCut := [⟨38,241859843,241860000⟩,
⟨102,649425839,649426259⟩,
⟨128,817954355,817954882⟩]
theorem checked15961 : checkPrefixCuts (2^48) 2095972353 9 Manual.Count131072.C015961.packed 128 cuts15961 = true := by
 decide +kernel
def pointBounds15961 : List (Nat × Nat × Nat) := [(2096011264,97083048758144,97083427325681),(2096076800,97083456324140,97083834891940)]
theorem point_links_checked15961 : (cuts15961.take 2).map (fun c => (2095972353-1+2*2^9*c.k,97082806898301+c.lower,97083185465681+c.upper)) = pointBounds15961 := by
 decide +kernel
def cuts15962 : List PrefixCut := [⟨38,241307574,241307731⟩,
⟨102,650728052,650728476⟩,
⟨128,813337860,813338387⟩]
theorem checked15962 : checkPrefixCuts (2^48) 2096103425 9 Manual.Count131072.C015962.packed 128 cuts15962 = true := by
 decide +kernel
def pointBounds15962 : List (Nat × Nat × Nat) := [(2096142336,97083866160230,97084244728294),(2096207872,97084275580708,97084654149039)]
theorem point_links_checked15962 : (cuts15962.take 2).map (fun c => (2096103425-1+2*2^9*c.k,97083624852656+c.lower,97084003420563+c.upper)) = pointBounds15962 := by
 decide +kernel
def cuts15963 : List PrefixCut := [⟨38,246663516,246663676⟩,
⟨102,649881886,649882305⟩,
⟨128,814226993,814227518⟩]
theorem checked15963 : checkPrefixCuts (2^48) 2096234497 9 Manual.Count131072.C015963.packed 128 cuts15963 = true := by
 decide +kernel
def pointBounds15963 : List (Nat × Nat × Nat) := [(2096273408,97084684854032,97085063422626),(2096338944,97085088072402,97085466641255)]
theorem point_links_checked15963 : (cuts15963.take 2).map (fun c => (2096234497-1+2*2^9*c.k,97084438190516+c.lower,97084816758950+c.upper)) = pointBounds15963 := by
 decide +kernel
def cuts15964 : List PrefixCut := [⟨38,245842494,245842651⟩,
⟨102,654540342,654540762⟩,
⟨128,816861296,816861820⟩]
theorem checked15964 : checkPrefixCuts (2^48) 2096365569 9 Manual.Count131072.C015964.packed 128 cuts15964 = true := by
 decide +kernel
def pointBounds15964 : List (Nat × Nat × Nat) := [(2096404480,97085498260003,97085876829119),(2096470016,97085906957851,97086285527230)]
theorem point_links_checked15964 : (cuts15964.take 2).map (fun c => (2096365569-1+2*2^9*c.k,97085252417509+c.lower,97085630986468+c.upper)) = pointBounds15964 := by
 decide +kernel
def cuts15965 : List PrefixCut := [⟨38,238845667,238845824⟩,
⟨102,653156785,653157200⟩,
⟨128,820032144,820032670⟩]
theorem checked15965 : checkPrefixCuts (2^48) 2096496641 9 Manual.Count131072.C015965.packed 128 cuts15965 = true := by
 decide +kernel
def pointBounds15965 : List (Nat × Nat × Nat) := [(2096535552,97086308124472,97086686694112),(2096601088,97086722435590,97087101005488)]
theorem point_links_checked15965 : (cuts15965.take 2).map (fun c => (2096496641-1+2*2^9*c.k,97086069278805+c.lower,97086447848288+c.upper)) = pointBounds15965 := by
 decide +kernel
def cuts15966 : List PrefixCut := [⟨38,242321256,242321413⟩,
⟨102,662781855,662782282⟩,
⟨128,825887957,825888485⟩]
theorem checked15966 : checkPrefixCuts (2^48) 2096627713 9 Manual.Count131072.C015966.packed 128 cuts15966 = true := by
 decide +kernel
def pointBounds15966 : List (Nat × Nat × Nat) := [(2096666624,97087131632205,97087510202371),(2096732160,97087552092804,97087930663240)]
theorem point_links_checked15966 : (cuts15966.take 2).map (fun c => (2096627713-1+2*2^9*c.k,97086889310949+c.lower,97087267880958+c.upper)) = pointBounds15966 := by
 decide +kernel
def cuts15967 : List PrefixCut := [⟨38,242171840,242172000⟩,
⟨102,656028451,656028879⟩,
⟨128,816708123,816708654⟩]
theorem checked15967 : checkPrefixCuts (2^48) 2096758785 9 Manual.Count131072.C015967.packed 128 cuts15967 = true := by
 decide +kernel
def pointBounds15967 : List (Nat × Nat × Nat) := [(2096797696,97087957370746,97088335941443),(2096863232,97088371227357,97088749798322)]
theorem point_links_checked15967 : (cuts15967.take 2).map (fun c => (2096758785-1+2*2^9*c.k,97087715198906+c.lower,97088093769443+c.upper)) = pointBounds15967 := by
 decide +kernel
def cuts15968 : List PrefixCut := [⟨38,244036045,244036201⟩,
⟨102,663907110,663907538⟩,
⟨128,828469308,828469838⟩]
theorem checked15968 : checkPrefixCuts (2^48) 2096889857 9 Manual.Count131072.C015968.packed 128 cuts15968 = true := by
 decide +kernel
def pointBounds15968 : List (Nat × Nat × Nat) := [(2096928768,97088775943074,97089154514298),(2096994304,97089195814139,97089574385635)]
theorem point_links_checked15968 : (cuts15968.take 2).map (fun c => (2096889857-1+2*2^9*c.k,97088531907029+c.lower,97088910478097+c.upper)) = pointBounds15968 := by
 decide +kernel
def cuts15969 : List PrefixCut := [⟨38,246436776,246436935⟩,
⟨102,656214942,656215366⟩,
⟨128,814727042,814727570⟩]
theorem checked15969 : checkPrefixCuts (2^48) 2097020929 9 Manual.Count131072.C015969.packed 128 cuts15969 = true := by
 decide +kernel
def pointBounds15969 : List (Nat × Nat × Nat) := [(2097059840,97089606813113,97089985384870),(2097125376,97090016591279,97090395163301)]
theorem point_links_checked15969 : (cuts15969.take 2).map (fun c => (2097020929-1+2*2^9*c.k,97089360376337+c.lower,97089738947935+c.upper)) = pointBounds15969 := by
 decide +kernel
def cuts15970 : List PrefixCut := [⟨38,242663305,242663461⟩,
⟨103,665300177,665300607⟩,
⟨128,832257558,832258091⟩]
theorem checked15970 : checkPrefixCuts (2^48) 2097152001 9 Manual.Count131072.C015970.packed 128 cuts15970 = true := by
 decide +kernel
def pointBounds15970 : List (Nat × Nat × Nat) := [(2097190912,97090417766684,97090796338966),(2097257472,97090840403556,97091218976112)]
theorem point_links_checked15970 : (cuts15970.take 2).map (fun c => (2097152001-1+2*2^9*c.k,97090175103379+c.lower,97090553675505+c.upper)) = pointBounds15970 := by
 decide +kernel
def cuts15971 : List PrefixCut := [⟨40,251103118,251103278⟩,
⟨105,661903175,661903605⟩,
⟨128,807109375,807109899⟩]
theorem checked15971 : checkPrefixCuts (2^48) 2097283073 9 Manual.Count131072.C015971.packed 128 cuts15971 = true := by
 decide +kernel
def pointBounds15971 : List (Nat × Nat × Nat) := [(2097324032,97091258464055,97091637036874),(2097390592,97091669264112,97092047837201)]
theorem point_links_checked15971 : (cuts15971.take 2).map (fun c => (2097283073-1+2*2^9*c.k,97091007360937+c.lower,97091385933596+c.upper)) = pointBounds15971 := by
 decide +kernel
def cuts15972 : List PrefixCut := [⟨42,275109060,275109238⟩,
⟨107,689238064,689238512⟩,
⟨128,825712559,825713094⟩]
theorem checked15972 : checkPrefixCuts (2^48) 2097414145 9 Manual.Count131072.C015972.packed 128 cuts15972 = true := by
 decide +kernel
def pointBounds15972 : List (Nat × Nat × Nat) := [(2097457152,97092089579372,97092468152733),(2097523712,97092503708376,97092882282007)]
theorem point_links_checked15972 : (cuts15972.take 2).map (fun c => (2097414145-1+2*2^9*c.k,97091814470312+c.lower,97092193043495+c.upper)) = pointBounds15972 := by
 decide +kernel
def cuts15973 : List PrefixCut := [⟨44,283679953,283680139⟩,
⟨109,704894537,704894992⟩,
⟨128,824050593,824051126⟩]
theorem checked15973 : checkPrefixCuts (2^48) 2097545217 9 Manual.Count131072.C015973.packed 128 cuts15973 = true := by
 decide +kernel
def pointBounds15973 : List (Nat × Nat × Nat) := [(2097590272,97092923862824,97093302436728),(2097656832,97093345077408,97093723651581)]
theorem point_links_checked15973 : (cuts15973.take 2).map (fun c => (2097545217-1+2*2^9*c.k,97092640182871+c.lower,97093018756589+c.upper)) = pointBounds15973 := by
 decide +kernel
def cuts15974 : List PrefixCut := [⟨46,296409458,296409650⟩,
⟨111,703776928,703777388⟩,
⟨128,810178731,810179261⟩]
theorem checked15974 : checkPrefixCuts (2^48) 2097676289 9 Manual.Count131072.C015974.packed 128 cuts15974 = true := by
 decide +kernel
def pointBounds15974 : List (Nat × Nat × Nat) := [(2097723392,97093760642922,97094139217365),(2097789952,97094168010392,97094546585103)]
theorem point_links_checked15974 : (cuts15974.take 2).map (fun c => (2097676289-1+2*2^9*c.k,97093464233464+c.lower,97093842807715+c.upper)) = pointBounds15974 := by
 decide +kernel
def cuts15975 : List PrefixCut := [⟨48,303502070,303502267⟩,
⟨113,706952668,706953125⟩,
⟨128,800870174,800870691⟩]
theorem checked15975 : checkPrefixCuts (2^48) 2097807361 9 Manual.Count131072.C015975.packed 128 cuts15975 = true := by
 decide +kernel
def pointBounds15975 : List (Nat × Nat × Nat) := [(2097856512,97094577914265,97094956489243),(2097923072,97094981364863,97095359940101)]
theorem point_links_checked15975 : (cuts15975.take 2).map (fun c => (2097807361-1+2*2^9*c.k,97094274412195+c.lower,97094652986976+c.upper)) = pointBounds15975 := by
 decide +kernel
def cuts15976 : List PrefixCut := [⟨50,323741933,323742136⟩,
⟨115,740046519,740046993⟩,
⟨128,821347135,821347659⟩]
theorem checked15976 : checkPrefixCuts (2^48) 2097938433 9 Manual.Count131072.C015976.packed 128 cuts15976 = true := by
 decide +kernel
def pointBounds15976 : List (Nat × Nat × Nat) := [(2097989632,97095399024302,97095777599803),(2098056192,97095815328888,97096193904660)]
theorem point_links_checked15976 : (cuts15976.take 2).map (fun c => (2097938433-1+2*2^9*c.k,97095075282369+c.lower,97095453857667+c.upper)) = pointBounds15976 := by
 decide +kernel
def cuts15977 : List PrefixCut := [⟨52,336466508,336466724⟩,
⟨117,751939754,751940237⟩,
⟨128,819551841,819552370⟩]
theorem checked15977 : checkPrefixCuts (2^48) 2098069505 9 Manual.Count131072.C015977.packed 128 cuts15977 = true := by
 decide +kernel
def pointBounds15977 : List (Nat × Nat × Nat) := [(2098122752,97096233096012,97096611672050),(2098189312,97096648569258,97097027145563)]
theorem point_links_checked15977 : (cuts15977.take 2).map (fun c => (2098069505-1+2*2^9*c.k,97095896629504+c.lower,97096275205326+c.upper)) = pointBounds15977 := by
 decide +kernel
def cuts15978 : List PrefixCut := [⟨54,346908841,346909061⟩,
⟨119,761014198,761014686⟩,
⟨128,818829622,818830147⟩]
theorem checked15978 : checkPrefixCuts (2^48) 2098200577 9 Manual.Count131072.C015978.packed 128 cuts15978 = true := by
 decide +kernel
def pointBounds15978 : List (Nat × Nat × Nat) := [(2098255872,97097063090186,97097441666757),(2098322432,97097477195543,97097855772382)]
theorem point_links_checked15978 : (cuts15978.take 2).map (fun c => (2098200577-1+2*2^9*c.k,97096716181345+c.lower,97097094757696+c.upper)) = pointBounds15978 := by
 decide +kernel
def cuts15979 : List PrefixCut := [⟨56,354801333,354801565⟩,
⟨121,762978547,762979039⟩,
⟨128,809388940,809389462⟩]
theorem checked15979 : checkPrefixCuts (2^48) 2098331649 9 Manual.Count131072.C015979.packed 128 cuts15979 = true := by
 decide +kernel
def pointBounds15979 : List (Nat × Nat × Nat) := [(2098388992,97097889812300,97098268389408),(2098455552,97098297989514,97098676566882)]
theorem point_links_checked15979 : (cuts15979.take 2).map (fun c => (2098331649-1+2*2^9*c.k,97097535010967+c.lower,97097913587843+c.upper)) = pointBounds15979 := by
 decide +kernel
def cuts15980 : List PrefixCut := [⟨58,369399335,369399566⟩,
⟨123,788146685,788147185⟩,
⟨128,818861456,818861976⟩]
theorem checked15980 : checkPrefixCuts (2^48) 2098462721 9 Manual.Count131072.C015980.packed 128 cuts15980 = true := by
 decide +kernel
def pointBounds15980 : List (Nat × Nat × Nat) := [(2098522112,97098713799242,97099092376871),(2098588672,97099132546592,97099511124490)]
theorem point_links_checked15980 : (cuts15980.take 2).map (fun c => (2098462721-1+2*2^9*c.k,97098344399907+c.lower,97098722977305+c.upper)) = pointBounds15980 := by
 decide +kernel
def cuts15981 : List PrefixCut := [⟨60,387482776,387483025⟩,
⟨125,802448277,802448795⟩,
⟨128,821627036,821627567⟩]
theorem checked15981 : checkPrefixCuts (2^48) 2098593793 9 Manual.Count131072.C015981.packed 128 cuts15981 = true := by
 decide +kernel
def pointBounds15981 : List (Nat × Nat × Nat) := [(2098655232,97099550744139,97099929322306),(2098721792,97099965709640,97100344288076)]
theorem point_links_checked15981 : (cuts15981.take 2).map (fun c => (2098593793-1+2*2^9*c.k,97099163261363+c.lower,97099541839281+c.upper)) = pointBounds15981 := by
 decide +kernel
def cuts15982 : List PrefixCut := [⟨62,392286528,392286786⟩,
⟨127,814870045,814870573⟩,
⟨128,821173156,821173689⟩]
theorem checked15982 : checkPrefixCuts (2^48) 2098724865 9 Manual.Count131072.C015982.packed 128 cuts15982 = true := by
 decide +kernel
def pointBounds15982 : List (Nat × Nat × Nat) := [(2098788352,97100377174927,97100755753634),(2098854912,97100799758444,97101178337421)]
theorem point_links_checked15982 : (cuts15982.take 2).map (fun c => (2098724865-1+2*2^9*c.k,97099984888399+c.lower,97100363466848+c.upper)) = pointBounds15982 := by
 decide +kernel
def cuts15983 : List PrefixCut := [⟨64,408488783,408489051⟩,
⟨128,816026041,816026571⟩]
theorem checked15983 : checkPrefixCuts (2^48) 2098855937 9 Manual.Count131072.C015983.packed 128 cuts15983 = true := by
 decide +kernel
def pointBounds15983 : List (Nat × Nat × Nat) := [(2098921472,97101214550338,97101593129588)]
theorem point_links_checked15983 : (cuts15983.take 1).map (fun c => (2098855937-1+2*2^9*c.k,97100806061555+c.lower,97101184640537+c.upper)) = pointBounds15983 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000186
