import PlattAssemblyKernel
import PlattCertificates.Count131072.C019120
import PlattCertificates.Count131072.C019121
import PlattCertificates.Count131072.C019122
import PlattCertificates.Count131072.C019123
import PlattCertificates.Count131072.C019124
import PlattCertificates.Count131072.C019125
import PlattCertificates.Count131072.C019126
import PlattCertificates.Count131072.C019127
import PlattCertificates.Count131072.C019128
import PlattCertificates.Count131072.C019129
import PlattCertificates.Count131072.C019130
import PlattCertificates.Count131072.C019131
import PlattCertificates.Count131072.C019132
import PlattCertificates.Count131072.C019133
import PlattCertificates.Count131072.C019134
import PlattCertificates.Count131072.C019135
import PlattCertificates.Count131072.C019136
import PlattCertificates.Count131072.C019137
import PlattCertificates.Count131072.C019138
import PlattCertificates.Count131072.C019139
import PlattCertificates.Count131072.C019140
import PlattCertificates.Count131072.C019141
import PlattCertificates.Count131072.C019142
import PlattCertificates.Count131072.C019143
import PlattCertificates.Count131072.C019144
import PlattCertificates.Count131072.C019145
import PlattCertificates.Count131072.C019146
import PlattCertificates.Count131072.C019147
import PlattCertificates.Count131072.C019148
import PlattCertificates.Count131072.C019149
import PlattCertificates.Count131072.C019150
import PlattCertificates.Count131072.C019151
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000285
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts19120 : List PrefixCut := [⟨11,61116220,61116256⟩,
⟨88,472437831,472438111⟩,
⟨128,684709686,684710088⟩]
theorem checked19120 : checkPrefixCuts (2^48) 2510028801 9 Manual.Count131072.C019120.packed 128 cuts19120 = true := by
 decide +kernel
def pointBounds19120 : List (Nat × Nat × Nat) := [(2510040064,99437093682821,99437473706801),(2510118912,99437505004432,99437885028656)]
theorem point_links_checked19120 : (cuts19120.take 2).map (fun c => (2510028801-1+2*2^9*c.k,99437032566601+c.lower,99437412590545+c.upper)) = pointBounds19120 := by
 decide +kernel
def cuts19121 : List PrefixCut := [⟨37,190290392,190290507⟩,
⟨114,596203865,596204226⟩,
⟨128,671778615,671779021⟩]
theorem checked19121 : checkPrefixCuts (2^48) 2510159873 9 Manual.Count131072.C019121.packed 128 cuts19121 = true := by
 decide +kernel
def pointBounds19121 : List (Nat × Nat × Nat) := [(2510197760,99437907566679,99438287591140),(2510276608,99438313480152,99438693504859)]
theorem point_links_checked19121 : (cuts19121.take 2).map (fun c => (2510159873-1+2*2^9*c.k,99437717276287+c.lower,99438097300633+c.upper)) = pointBounds19121 := by
 decide +kernel
def cuts19122 : List PrefixCut := [⟨63,333353455,333353654⟩,
⟨128,679256131,679256533⟩]
theorem checked19122 : checkPrefixCuts (2^48) 2510290945 9 Manual.Count131072.C019122.packed 128 cuts19122 = true := by
 decide +kernel
def pointBounds19122 : List (Nat × Nat × Nat) := [(2510355456,99438722408357,99439102433308)]
theorem point_links_checked19122 : (cuts19122.take 1).map (fun c => (2510290945-1+2*2^9*c.k,99438389054902+c.lower,99438769079654+c.upper)) = pointBounds19122 := by
 decide +kernel
def cuts19123 : List PrefixCut := [⟨12,63124836,63124873⟩,
⟨89,472027313,472027595⟩,
⟨128,676866124,676866526⟩]
theorem checked19123 : checkPrefixCuts (2^48) 2510422017 9 Manual.Count131072.C019123.packed 128 cuts19123 = true := by
 decide +kernel
def pointBounds19123 : List (Nat × Nat × Nat) := [(2510434304,99439131435869,99439511461060),(2510513152,99439540338346,99439920363782)]
theorem point_links_checked19123 : (cuts19123.take 2).map (fun c => (2510422017-1+2*2^9*c.k,99439068311033+c.lower,99439448336187+c.upper)) = pointBounds19123 := by
 decide +kernel
def cuts19124 : List PrefixCut := [⟨38,204835579,204835701⟩,
⟨115,609788420,609788779⟩,
⟨128,679521543,679521945⟩]
theorem checked19124 : checkPrefixCuts (2^48) 2510553089 9 Manual.Count131072.C019124.packed 128 cuts19124 = true := by
 decide +kernel
def pointBounds19124 : List (Nat × Nat × Nat) := [(2510592000,99439950012736,99440330038414),(2510670848,99440354965577,99440734991492)]
theorem point_links_checked19124 : (cuts19124.take 2).map (fun c => (2510553089-1+2*2^9*c.k,99439745177157+c.lower,99440125202713+c.upper)) = pointBounds19124 := by
 decide +kernel
def cuts19125 : List PrefixCut := [⟨64,343839414,343839620⟩,
⟨128,682288771,682289184⟩]
theorem checked19125 : checkPrefixCuts (2^48) 2510684161 9 Manual.Count131072.C019125.packed 128 cuts19125 = true := by
 decide +kernel
def pointBounds19125 : List (Nat × Nat × Nat) := [(2510749696,99440768538114,99441148564278)]
theorem point_links_checked19125 : (cuts19125.take 1).map (fun c => (2510684161-1+2*2^9*c.k,99440424698700+c.lower,99440804724658+c.upper)) = pointBounds19125 := by
 decide +kernel
def cuts19126 : List PrefixCut := [⟨13,69729111,69729153⟩,
⟨90,473971188,473971472⟩,
⟨128,676199563,676199968⟩]
theorem checked19126 : checkPrefixCuts (2^48) 2510815233 9 Manual.Count131072.C019126.packed 128 cuts19126 = true := by
 decide +kernel
def pointBounds19126 : List (Nat × Nat × Nat) := [(2510828544,99441176716582,99441556742995),(2510907392,99441580958659,99441960985314)]
theorem point_links_checked19126 : (cuts19126.take 2).map (fun c => (2510815233-1+2*2^9*c.k,99441106987471+c.lower,99441487013842+c.upper)) = pointBounds19126 := by
 decide +kernel
def cuts19127 : List PrefixCut := [⟨39,206148676,206148798⟩,
⟨116,620453928,620454296⟩,
⟨128,689391463,689391873⟩]
theorem checked19127 : checkPrefixCuts (2^48) 2510946305 9 Manual.Count131072.C019127.packed 128 cuts19127 = true := by
 decide +kernel
def pointBounds19127 : List (Nat × Nat × Nat) := [(2510986240,99441989335710,99442369362608),(2511065088,99442403640962,99442783668106)]
theorem point_links_checked19127 : (cuts19127.take 2).map (fun c => (2510946305-1+2*2^9*c.k,99441783187034+c.lower,99442163213810+c.upper)) = pointBounds19127 := by
 decide +kernel
def cuts19128 : List PrefixCut := [⟨65,345354834,345355039⟩,
⟨128,680276317,680276725⟩]
theorem checked19128 : checkPrefixCuts (2^48) 2511077377 9 Manual.Count131072.C019128.packed 128 cuts19128 = true := by
 decide +kernel
def pointBounds19128 : List (Nat × Nat × Nat) := [(2511143936,99442817933331,99443197960722)]
theorem point_links_checked19128 : (cuts19128.take 1).map (fun c => (2511077377-1+2*2^9*c.k,99442472578497+c.lower,99442852605683+c.upper)) = pointBounds19128 := by
 decide +kernel
def cuts19129 : List PrefixCut := [⟨14,69942354,69942396⟩,
⟨91,481294459,481294751⟩,
⟨128,673067482,673067888⟩]
theorem checked19129 : checkPrefixCuts (2^48) 2511208449 9 Manual.Count131072.C019129.packed 128 cuts19129 = true := by
 decide +kernel
def pointBounds19129 : List (Nat × Nat × Nat) := [(2511222784,99443222797168,99443602824804),(2511301632,99443634149273,99444014177159)]
theorem point_links_checked19129 : (cuts19129.take 2).map (fun c => (2511208449-1+2*2^9*c.k,99443152854814+c.lower,99443532882408+c.upper)) = pointBounds19129 := by
 decide +kernel
def cuts19130 : List PrefixCut := [⟨40,214074061,214074189⟩,
⟨117,621701704,621702075⟩,
⟨128,679308758,679309164⟩]
theorem checked19130 : checkPrefixCuts (2^48) 2511339521 9 Manual.Count131072.C019130.packed 128 cuts19130 = true := by
 decide +kernel
def pointBounds19130 : List (Nat × Nat × Nat) := [(2511380480,99444039996357,99444420024485),(2511459328,99444447624000,99444827652371)]
theorem point_links_checked19130 : (cuts19130.take 2).map (fun c => (2511339521-1+2*2^9*c.k,99443825922296+c.lower,99444205950296+c.upper)) = pointBounds19130 := by
 decide +kernel
def cuts19131 : List PrefixCut := [⟨66,349447352,349447560⟩,
⟨128,673893746,673894147⟩]
theorem checked19131 : checkPrefixCuts (2^48) 2511470593 9 Manual.Count131072.C019131.packed 128 cuts19131 = true := by
 decide +kernel
def pointBounds19131 : List (Nat × Nat × Nat) := [(2511538176,99444854678406,99445234707020)]
theorem point_links_checked19131 : (cuts19131.take 1).map (fun c => (2511470593-1+2*2^9*c.k,99444505231054+c.lower,99444885259460+c.upper)) = pointBounds19131 := by
 decide +kernel
def cuts19132 : List PrefixCut := [⟨15,81810767,81810814⟩,
⟨92,491081057,491081345⟩,
⟨128,683272267,683272672⟩]
theorem checked19132 : checkPrefixCuts (2^48) 2511601665 9 Manual.Count131072.C019132.packed 128 cuts19132 = true := by
 decide +kernel
def pointBounds19132 : List (Nat × Nat × Nat) := [(2511617024,99445260935567,99445640964421),(2511695872,99445670205857,99446050234952)]
theorem point_links_checked19132 : (cuts19132.take 2).map (fun c => (2511601665-1+2*2^9*c.k,99445179124800+c.lower,99445559153607+c.upper)) = pointBounds19132 := by
 decide +kernel
def cuts19133 : List PrefixCut := [⟨41,213816370,213816501⟩,
⟨118,618242359,618242735⟩,
⟨128,669340994,669341401⟩]
theorem checked19133 : checkPrefixCuts (2^48) 2511732737 9 Manual.Count131072.C019133.packed 128 cuts19133 = true := by
 decide +kernel
def pointBounds19133 : List (Nat × Nat × Nat) := [(2511774720,99446076213437,99446456242780),(2511853568,99446480639426,99446860669014)]
theorem point_links_checked19133 : (cuts19133.take 2).map (fun c => (2511732737-1+2*2^9*c.k,99445862397067+c.lower,99446242426279+c.upper)) = pointBounds19133 := by
 decide +kernel
def cuts19134 : List PrefixCut := [⟨67,348160049,348160253⟩,
⟨128,676477433,676477829⟩]
theorem checked19134 : checkPrefixCuts (2^48) 2511863809 9 Manual.Count131072.C019134.packed 128 cuts19134 = true := by
 decide +kernel
def pointBounds19134 : List (Nat × Nat × Nat) := [(2511932416,99446879898110,99447259927933)]
theorem point_links_checked19134 : (cuts19134.take 1).map (fun c => (2511863809-1+2*2^9*c.k,99446531738061+c.lower,99446911767680+c.upper)) = pointBounds19134 := by
 decide +kernel
def cuts19135 : List PrefixCut := [⟨16,85047446,85047498⟩,
⟨93,490779937,490780229⟩,
⟨128,679803706,679804111⟩]
theorem checked19135 : checkPrefixCuts (2^48) 2511994881 9 Manual.Count131072.C019135.packed 128 cuts19135 = true := by
 decide +kernel
def pointBounds19135 : List (Nat × Nat × Nat) := [(2512011264,99447293262940,99447673293007),(2512090112,99447698995431,99448079025738)]
theorem point_links_checked19135 : (cuts19135.take 2).map (fun c => (2511994881-1+2*2^9*c.k,99447208215494+c.lower,99447588245509+c.upper)) = pointBounds19135 := by
 decide +kernel
def cuts19136 : List PrefixCut := [⟨42,221401946,221402075⟩,
⟨119,629685961,629686339⟩,
⟨128,679768223,679768630⟩]
theorem checked19136 : checkPrefixCuts (2^48) 2512125953 9 Manual.Count131072.C019136.packed 128 cuts19136 = true := by
 decide +kernel
def pointBounds19136 : List (Nat × Nat × Nat) := [(2512168960,99448109421146,99448489451695),(2512247808,99448517705161,99448897735959)]
theorem point_links_checked19136 : (cuts19136.take 2).map (fun c => (2512125953-1+2*2^9*c.k,99447888019200+c.lower,99448268049620+c.upper)) = pointBounds19136 := by
 decide +kernel
def cuts19137 : List PrefixCut := [⟨68,363678879,363679101⟩,
⟨128,675811702,675812112⟩]
theorem checked19137 : checkPrefixCuts (2^48) 2512257025 9 Manual.Count131072.C019137.packed 128 cuts19137 = true := by
 decide +kernel
def pointBounds19137 : List (Nat × Nat × Nat) := [(2512326656,99448931466302,99449311497351)]
theorem point_links_checked19137 : (cuts19137.take 1).map (fun c => (2512257025-1+2*2^9*c.k,99448567787423+c.lower,99448947818250+c.upper)) = pointBounds19137 := by
 decide +kernel
def cuts19138 : List PrefixCut := [⟨17,92652459,92652512⟩,
⟨94,500673954,500674254⟩,
⟨128,684066641,684067044⟩]
theorem checked19138 : checkPrefixCuts (2^48) 2512388097 9 Manual.Count131072.C019138.packed 128 cuts19138 = true := by
 decide +kernel
def pointBounds19138 : List (Nat × Nat × Nat) := [(2512405504,99449336251584,99449716282874),(2512484352,99449744273079,99450124304616)]
theorem point_links_checked19138 : (cuts19138.take 2).map (fun c => (2512388097-1+2*2^9*c.k,99449243599125+c.lower,99449623630362+c.upper)) = pointBounds19138 := by
 decide +kernel
def cuts19139 : List PrefixCut := [⟨43,227976932,227977067⟩,
⟨120,631155766,631156146⟩,
⟨128,675853056,675853464⟩]
theorem checked19139 : checkPrefixCuts (2^48) 2512519169 9 Manual.Count131072.C019139.packed 128 cuts19139 = true := by
 decide +kernel
def pointBounds19139 : List (Nat × Nat × Nat) := [(2512563200,99450155642698,99450535674473),(2512642048,99450558821532,99450938853552)]
theorem point_links_checked19139 : (cuts19139.take 2).map (fun c => (2512519169-1+2*2^9*c.k,99449927665766+c.lower,99450307697406+c.upper)) = pointBounds19139 := by
 decide +kernel
def cuts19140 : List PrefixCut := [⟨69,361269450,361269664⟩,
⟨128,678058066,678058471⟩]
theorem checked19140 : checkPrefixCuts (2^48) 2512650241 9 Manual.Count131072.C019140.packed 128 cuts19140 = true := by
 decide +kernel
def pointBounds19140 : List (Nat × Nat × Nat) := [(2512720896,99450964788272,99451344820534)]
theorem point_links_checked19140 : (cuts19140.take 1).map (fun c => (2512650241-1+2*2^9*c.k,99450603518822+c.lower,99450983550870+c.upper)) = pointBounds19140 := by
 decide +kernel
def cuts19141 : List PrefixCut := [⟨18,97678699,97678755⟩,
⟨95,510116821,510117123⟩,
⟨128,685415886,685416292⟩]
theorem checked19141 : checkPrefixCuts (2^48) 2512781313 9 Manual.Count131072.C019141.packed 128 cuts19141 = true := by
 decide +kernel
def pointBounds19141 : List (Nat × Nat × Nat) := [(2512799744,99451379255587,99451759288096),(2512878592,99451791693709,99452171726464)]
theorem point_links_checked19141 : (cuts19141.take 2).map (fun c => (2512781313-1+2*2^9*c.k,99451281576888+c.lower,99451661609341+c.upper)) = pointBounds19141 := by
 decide +kernel
def cuts19142 : List PrefixCut := [⟨44,230293426,230293557⟩,
⟨121,642593662,642594039⟩,
⟨128,682355700,682356101⟩]
theorem checked19142 : checkPrefixCuts (2^48) 2512912385 9 Manual.Count131072.C019142.packed 128 cuts19142 = true := by
 decide +kernel
def pointBounds19142 : List (Nat × Nat × Nat) := [(2512957440,99452197286200,99452577319190),(2513036288,99452609586436,99452989619672)]
theorem point_links_checked19142 : (cuts19142.take 2).map (fun c => (2512912385-1+2*2^9*c.k,99451966992774+c.lower,99452347025633+c.upper)) = pointBounds19142 := by
 decide +kernel
def cuts19143 : List PrefixCut := [⟨70,376445332,376445553⟩,
⟨128,680080223,680080623⟩]
theorem checked19143 : checkPrefixCuts (2^48) 2513043457 9 Manual.Count131072.C019143.packed 128 cuts19143 = true := by
 decide +kernel
def pointBounds19143 : List (Nat × Nat × Nat) := [(2513115136,99453025793806,99453405827287)]
theorem point_links_checked19143 : (cuts19143.take 1).map (fun c => (2513043457-1+2*2^9*c.k,99452649348474+c.lower,99453029381734+c.upper)) = pointBounds19143 := by
 decide +kernel
def cuts19144 : List PrefixCut := [⟨19,102031368,102031429⟩,
⟨96,511044828,511045129⟩,
⟨128,682620600,682621003⟩]
theorem checked19144 : checkPrefixCuts (2^48) 2513174529 9 Manual.Count131072.C019144.packed 128 cuts19144 = true := by
 decide +kernel
def pointBounds19144 : List (Nat × Nat × Nat) := [(2513193984,99453431460065,99453811493786),(2513272832,99453840473525,99454220507486)]
theorem point_links_checked19144 : (cuts19144.take 2).map (fun c => (2513174529-1+2*2^9*c.k,99453329428697+c.lower,99453709462357+c.upper)) = pointBounds19144 := by
 decide +kernel
def cuts19145 : List PrefixCut := [⟨45,240112728,240112874⟩,
⟨122,640701226,640701611⟩,
⟨128,674745636,674746044⟩]
theorem checked19145 : checkPrefixCuts (2^48) 2513305601 9 Manual.Count131072.C019145.packed 128 cuts19145 = true := by
 decide +kernel
def pointBounds19145 : List (Nat × Nat × Nat) := [(2513351680,99454252162025,99454632196234),(2513430528,99454652750523,99455032784971)]
theorem point_links_checked19145 : (cuts19145.take 2).map (fun c => (2513305601-1+2*2^9*c.k,99454012049297+c.lower,99454392083360+c.upper)) = pointBounds19145 := by
 decide +kernel
def cuts19146 : List PrefixCut := [⟨71,379074054,379074282⟩,
⟨128,678517993,678518399⟩]
theorem checked19146 : checkPrefixCuts (2^48) 2513436673 9 Manual.Count131072.C019146.packed 128 cuts19146 = true := by
 decide +kernel
def pointBounds19146 : List (Nat × Nat × Nat) := [(2513509376,99455065868987,99455445903686)]
theorem point_links_checked19146 : (cuts19146.take 1).map (fun c => (2513436673-1+2*2^9*c.k,99454686794933+c.lower,99455066829404+c.upper)) = pointBounds19146 := by
 decide +kernel
def cuts19147 : List PrefixCut := [⟨20,107502501,107502563⟩,
⟨97,526194017,526194325⟩,
⟨128,689008701,689009108⟩]
theorem checked19147 : checkPrefixCuts (2^48) 2513567745 9 Manual.Count131072.C019147.packed 128 cuts19147 = true := by
 decide +kernel
def pointBounds19147 : List (Nat × Nat × Nat) := [(2513588224,99455472815427,99455852850366),(2513667072,99455891506943,99456271542128)]
theorem point_links_checked19147 : (cuts19147.take 2).map (fun c => (2513567745-1+2*2^9*c.k,99455365312926+c.lower,99455745347803+c.upper)) = pointBounds19147 := by
 decide +kernel
def cuts19148 : List PrefixCut := [⟨46,241866688,241866832⟩,
⟨123,651126340,651126724⟩,
⟨128,678447178,678447578⟩]
theorem checked19148 : checkPrefixCuts (2^48) 2513698817 9 Manual.Count131072.C019148.packed 128 cuts19148 = true := by
 decide +kernel
def pointBounds19148 : List (Nat × Nat × Nat) := [(2513745920,99456296188315,99456676223743),(2513824768,99456705447967,99457085483635)]
theorem point_links_checked19148 : (cuts19148.take 2).map (fun c => (2513698817-1+2*2^9*c.k,99456054321627+c.lower,99456434356911+c.upper)) = pointBounds19148 := by
 decide +kernel
def cuts19149 : List PrefixCut := [⟨72,384389195,384389426⟩,
⟨128,676620418,676620821⟩]
theorem checked19149 : checkPrefixCuts (2^48) 2513829889 9 Manual.Count131072.C019149.packed 128 cuts19149 = true := by
 decide +kernel
def pointBounds19149 : List (Nat × Nat × Nat) := [(2513903616,99457117158000,99457497193915)]
theorem point_links_checked19149 : (cuts19149.take 1).map (fun c => (2513829889-1+2*2^9*c.k,99456732768805+c.lower,99457112804489+c.upper)) = pointBounds19149 := by
 decide +kernel
def cuts19150 : List PrefixCut := [⟨21,110732612,110732680⟩,
⟨98,521969033,521969347⟩,
⟨128,680615715,680616122⟩]
theorem checked19150 : checkPrefixCuts (2^48) 2513960961 9 Manual.Count131072.C019150.packed 128 cuts19150 = true := by
 decide +kernel
def pointBounds19150 : List (Nat × Nat × Nat) := [(2513982464,99457520121835,99457900157990),(2514061312,99457931358256,99458311394657)]
theorem point_links_checked19150 : (cuts19150.take 2).map (fun c => (2513960961-1+2*2^9*c.k,99457409389223+c.lower,99457789425310+c.upper)) = pointBounds19150 := by
 decide +kernel
def cuts19151 : List PrefixCut := [⟨47,248770206,248770353⟩,
⟨124,652479832,652480224⟩,
⟨128,673191159,673191563⟩]
theorem checked19151 : checkPrefixCuts (2^48) 2514092033 9 Manual.Count131072.C019151.packed 128 cuts19151 = true := by
 decide +kernel
def pointBounds19151 : List (Nat × Nat × Nat) := [(2514140160,99458338775144,99458718811785),(2514219008,99458742484770,99459122521656)]
theorem point_links_checked19151 : (cuts19151.take 2).map (fun c => (2514092033-1+2*2^9*c.k,99458090004938+c.lower,99458470041432+c.upper)) = pointBounds19151 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000285
