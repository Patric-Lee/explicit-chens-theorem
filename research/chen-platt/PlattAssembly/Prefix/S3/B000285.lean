import PlattAssemblyKernel
import PlattCertificates.Count131072.C029120
import PlattCertificates.Count131072.C029121
import PlattCertificates.Count131072.C029122
import PlattCertificates.Count131072.C029123
import PlattCertificates.Count131072.C029124
import PlattCertificates.Count131072.C029125
import PlattCertificates.Count131072.C029126
import PlattCertificates.Count131072.C029127
import PlattCertificates.Count131072.C029128
import PlattCertificates.Count131072.C029129
import PlattCertificates.Count131072.C029130
import PlattCertificates.Count131072.C029131
import PlattCertificates.Count131072.C029132
import PlattCertificates.Count131072.C029133
import PlattCertificates.Count131072.C029134
import PlattCertificates.Count131072.C029135
import PlattCertificates.Count131072.C029136
import PlattCertificates.Count131072.C029137
import PlattCertificates.Count131072.C029138
import PlattCertificates.Count131072.C029139
import PlattCertificates.Count131072.C029140
import PlattCertificates.Count131072.C029141
import PlattCertificates.Count131072.C029142
import PlattCertificates.Count131072.C029143
import PlattCertificates.Count131072.C029144
import PlattCertificates.Count131072.C029145
import PlattCertificates.Count131072.C029146
import PlattCertificates.Count131072.C029147
import PlattCertificates.Count131072.C029148
import PlattCertificates.Count131072.C029149
import PlattCertificates.Count131072.C029150
import PlattCertificates.Count131072.C029151
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000285
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts29120 : List PrefixCut := [⟨111,379763641,379763856⟩,
⟨128,438771489,438771738⟩]
theorem checked29120 : checkPrefixCuts (2^48) 3820748801 9 Manual.Count131072.C029120.packed 128 cuts29120 = true := by
 decide +kernel
def pointBounds29120 : List (Nat × Nat × Nat) := [(3820862464,104849262698287,104849645807056)]
theorem point_links_checked29120 : (cuts29120.take 1).map (fun c => (3820748801-1+2*2^9*c.k,104848882934646+c.lower,104849266043200+c.upper)) = pointBounds29120 := by
 decide +kernel
def cuts29121 : List PrefixCut := [⟨100,342033890,342034082⟩,
⟨128,437135802,437136049⟩]
theorem checked29121 : checkPrefixCuts (2^48) 3820879873 9 Manual.Count131072.C029121.packed 128 cuts29121 = true := by
 decide +kernel
def pointBounds29121 : List (Nat × Nat × Nat) := [(3820982272,104849663740025,104850046849020)]
theorem point_links_checked29121 : (cuts29121.take 1).map (fun c => (3820879873-1+2*2^9*c.k,104849321706135+c.lower,104849704814938+c.upper)) = pointBounds29121 := by
 decide +kernel
def cuts29122 : List PrefixCut := [⟨89,303864642,303864813⟩,
⟨128,435794877,435795120⟩]
theorem checked29122 : checkPrefixCuts (2^48) 3821010945 9 Manual.Count131072.C029122.packed 128 cuts29122 = true := by
 decide +kernel
def pointBounds29122 : List (Nat × Nat × Nat) := [(3821102080,104850062706579,104850445815800)]
theorem point_links_checked29122 : (cuts29122.take 1).map (fun c => (3821010945-1+2*2^9*c.k,104849758841937+c.lower,104850141950987+c.upper)) = pointBounds29122 := by
 decide +kernel
def cuts29123 : List PrefixCut := [⟨78,265550555,265550700⟩,
⟨128,438799991,438800236⟩]
theorem checked29123 : checkPrefixCuts (2^48) 3821142017 9 Manual.Count131072.C029123.packed 128 cuts29123 = true := by
 decide +kernel
def pointBounds29123 : List (Nat × Nat × Nat) := [(3821221888,104850460187369,104850843296807)]
theorem point_links_checked29123 : (cuts29123.take 1).map (fun c => (3821142017-1+2*2^9*c.k,104850194636814+c.lower,104850577746107+c.upper)) = pointBounds29123 := by
 decide +kernel
def cuts29124 : List PrefixCut := [⟨67,228122923,228123053⟩,
⟨128,436869860,436870107⟩]
theorem checked29124 : checkPrefixCuts (2^48) 3821273089 9 Manual.Count131072.C029124.packed 128 cuts29124 = true := by
 decide +kernel
def pointBounds29124 : List (Nat × Nat × Nat) := [(3821341696,104850861559728,104851244669396)]
theorem point_links_checked29124 : (cuts29124.take 1).map (fun c => (3821273089-1+2*2^9*c.k,104850633436805+c.lower,104851016546343+c.upper)) = pointBounds29124 := by
 decide +kernel
def cuts29125 : List PrefixCut := [⟨56,192318158,192318268⟩,
⟨128,435897381,435897628⟩]
theorem checked29125 : checkPrefixCuts (2^48) 3821404161 9 Manual.Count131072.C029125.packed 128 cuts29125 = true := by
 decide +kernel
def pointBounds29125 : List (Nat × Nat × Nat) := [(3821461504,104851262624823,104851645734718)]
theorem point_links_checked29125 : (cuts29125.take 1).map (fun c => (3821404161-1+2*2^9*c.k,104851070306665+c.lower,104851453416450+c.upper)) = pointBounds29125 := by
 decide +kernel
def cuts29126 : List PrefixCut := [⟨45,153274969,153275055⟩,
⟨128,435219497,435219743⟩]
theorem checked29126 : checkPrefixCuts (2^48) 3821535233 9 Manual.Count131072.C029126.packed 128 cuts29126 = true := by
 decide +kernel
def pointBounds29126 : List (Nat × Nat × Nat) := [(3821581312,104851659479015,104852042589133)]
theorem point_links_checked29126 : (cuts29126.take 1).map (fun c => (3821535233-1+2*2^9*c.k,104851506204046+c.lower,104851889314078+c.upper)) = pointBounds29126 := by
 decide +kernel
def cuts29127 : List PrefixCut := [⟨34,116443909,116443977⟩,
⟨128,437193160,437193405⟩]
theorem checked29127 : checkPrefixCuts (2^48) 3821666305 9 Manual.Count131072.C029127.packed 128 cuts29127 = true := by
 decide +kernel
def pointBounds29127 : List (Nat × Nat × Nat) := [(3821701120,104852057867452,104852440977798)]
theorem point_links_checked29127 : (cuts29127.take 1).map (fun c => (3821666305-1+2*2^9*c.k,104851941423543+c.lower,104852324533821+c.upper)) = pointBounds29127 := by
 decide +kernel
def cuts29128 : List PrefixCut := [⟨23,76669282,76669324⟩,
⟨128,440271362,440271608⟩]
theorem checked29128 : checkPrefixCuts (2^48) 3821797377 9 Manual.Count131072.C029128.packed 128 cuts29128 = true := by
 decide +kernel
def pointBounds29128 : List (Nat × Nat × Nat) := [(3821820928,104852455285985,104852838396550)]
theorem point_links_checked29128 : (cuts29128.take 1).map (fun c => (3821797377-1+2*2^9*c.k,104852378616703+c.lower,104852761727226+c.upper)) = pointBounds29128 := by
 decide +kernel
def cuts29129 : List PrefixCut := [⟨12,40432329,40432352⟩,
⟨128,439004240,439004487⟩]
theorem checked29129 : checkPrefixCuts (2^48) 3821928449 9 Manual.Count131072.C029129.packed 128 cuts29129 = true := by
 decide +kernel
def pointBounds29129 : List (Nat × Nat × Nat) := [(3821940736,104852859320394,104853242431186)]
theorem point_links_checked29129 : (cuts29129.take 1).map (fun c => (3821928449-1+2*2^9*c.k,104852818888065+c.lower,104853201998834+c.upper)) = pointBounds29129 := by
 decide +kernel
def cuts29130 : List PrefixCut := [⟨1,3461306,3461308⟩,
⟨118,398854051,398854279⟩,
⟨128,431256707,431256953⟩]
theorem checked29130 : checkPrefixCuts (2^48) 3822059521 9 Manual.Count131072.C029130.packed 128 cuts29130 = true := by
 decide +kernel
def pointBounds29130 : List (Nat × Nat × Nat) := [(3822060544,104853261353611,104853644464629),(3822180352,104853656746356,104854039857600)]
theorem point_links_checked29130 : (cuts29130.take 2).map (fun c => (3822059521-1+2*2^9*c.k,104853257892305+c.lower,104853641003321+c.upper)) = pointBounds29130 := by
 decide +kernel
def cuts29131 : List PrefixCut := [⟨107,364965965,364966169⟩,
⟨128,439710547,439710790⟩]
theorem checked29131 : checkPrefixCuts (2^48) 3822190593 9 Manual.Count131072.C029131.packed 128 cuts29131 = true := by
 decide +kernel
def pointBounds29131 : List (Nat × Nat × Nat) := [(3822300160,104854054114977,104854437226443)]
theorem point_links_checked29131 : (cuts29131.take 1).map (fun c => (3822190593-1+2*2^9*c.k,104853689149012+c.lower,104854072260274+c.upper)) = pointBounds29131 := by
 decide +kernel
def cuts29132 : List PrefixCut := [⟨96,331006516,331006703⟩,
⟨128,440652857,440653103⟩]
theorem checked29132 : checkPrefixCuts (2^48) 3822321665 9 Manual.Count131072.C029132.packed 128 cuts29132 = true := by
 decide +kernel
def pointBounds29132 : List (Nat × Nat × Nat) := [(3822419968,104854459866075,104854842977767)]
theorem point_links_checked29132 : (cuts29132.take 1).map (fun c => (3822321665-1+2*2^9*c.k,104854128859559+c.lower,104854511971064+c.upper)) = pointBounds29132 := by
 decide +kernel
def cuts29133 : List PrefixCut := [⟨85,288654746,288654907⟩,
⟨128,436072314,436072559⟩]
theorem checked29133 : checkPrefixCuts (2^48) 3822452737 9 Manual.Count131072.C029133.packed 128 cuts29133 = true := by
 decide +kernel
def pointBounds29133 : List (Nat × Nat × Nat) := [(3822539776,104854858167162,104855241279074)]
theorem point_links_checked29133 : (cuts29133.take 1).map (fun c => (3822452737-1+2*2^9*c.k,104854569512416+c.lower,104854952624167+c.upper)) = pointBounds29133 := by
 decide +kernel
def cuts29134 : List PrefixCut := [⟨74,250723744,250723886⟩,
⟨128,434363770,434364015⟩]
theorem checked29134 : checkPrefixCuts (2^48) 3822583809 9 Manual.Count131072.C029134.packed 128 cuts29134 = true := by
 decide +kernel
def pointBounds29134 : List (Nat × Nat × Nat) := [(3822659584,104855256308474,104855639420612)]
theorem point_links_checked29134 : (cuts29134.take 1).map (fun c => (3822583809-1+2*2^9*c.k,104855005584730+c.lower,104855388696726+c.upper)) = pointBounds29134 := by
 decide +kernel
def cuts29135 : List PrefixCut := [⟨63,212279839,212279958⟩,
⟨128,436778676,436778922⟩]
theorem checked29135 : checkPrefixCuts (2^48) 3822714881 9 Manual.Count131072.C029135.packed 128 cuts29135 = true := by
 decide +kernel
def pointBounds29135 : List (Nat × Nat × Nat) := [(3822779392,104855652228339,104856035340699)]
theorem point_links_checked29135 : (cuts29135.take 1).map (fun c => (3822714881-1+2*2^9*c.k,104855439948500+c.lower,104855823060741+c.upper)) = pointBounds29135 := by
 decide +kernel
def cuts29136 : List PrefixCut := [⟨52,175973692,175973791⟩,
⟨128,442138550,442138796⟩]
theorem checked29136 : checkPrefixCuts (2^48) 3822845953 9 Manual.Count131072.C029136.packed 128 cuts29136 = true := by
 decide +kernel
def pointBounds29136 : List (Nat × Nat × Nat) := [(3822899200,104856052700868,104856435813454)]
theorem point_links_checked29136 : (cuts29136.take 1).map (fun c => (3822845953-1+2*2^9*c.k,104855876727176+c.lower,104856259839663+c.upper)) = pointBounds29136 := by
 decide +kernel
def cuts29137 : List PrefixCut := [⟨41,141436976,141437055⟩,
⟨128,440356423,440356668⟩]
theorem checked29137 : checkPrefixCuts (2^48) 3822977025 9 Manual.Count131072.C029137.packed 128 cuts29137 = true := by
 decide +kernel
def pointBounds29137 : List (Nat × Nat × Nat) := [(3823019008,104856460302702,104856843415514)]
theorem point_links_checked29137 : (cuts29137.take 1).map (fun c => (3822977025-1+2*2^9*c.k,104856318865726+c.lower,104856701978459+c.upper)) = pointBounds29137 := by
 decide +kernel
def cuts29138 : List PrefixCut := [⟨30,102043319,102043375⟩,
⟨128,440046813,440047055⟩]
theorem checked29138 : checkPrefixCuts (2^48) 3823108097 9 Manual.Count131072.C029138.packed 128 cuts29138 = true := by
 decide +kernel
def pointBounds29138 : List (Nat × Nat × Nat) := [(3823138816,104856861265468,104857244378502)]
theorem point_links_checked29138 : (cuts29138.take 1).map (fun c => (3823108097-1+2*2^9*c.k,104856759222149+c.lower,104857142335127+c.upper)) = pointBounds29138 := by
 decide +kernel
def cuts29139 : List PrefixCut := [⟨19,63167601,63167634⟩,
⟨128,443786393,443786639⟩]
theorem checked29139 : checkPrefixCuts (2^48) 3823239169 9 Manual.Count131072.C029139.packed 128 cuts29139 = true := by
 decide +kernel
def pointBounds29139 : List (Nat × Nat × Nat) := [(3823258624,104857262436563,104857645549816)]
theorem point_links_checked29139 : (cuts29139.take 1).map (fun c => (3823239169-1+2*2^9*c.k,104857199268962+c.lower,104857582382182+c.upper)) = pointBounds29139 := by
 decide +kernel
def cuts29140 : List PrefixCut := [⟨8,25914063,25914077⟩,
⟨125,419035572,419035808⟩,
⟨128,429121112,429121354⟩]
theorem checked29140 : checkPrefixCuts (2^48) 3823370241 9 Manual.Count131072.C029140.packed 128 cuts29140 = true := by
 decide +kernel
def pointBounds29140 : List (Nat × Nat × Nat) := [(3823378432,104857668969418,104858052082898),(3823498240,104858062090927,104858445204629)]
theorem point_links_checked29140 : (cuts29140.take 2).map (fun c => (3823370241-1+2*2^9*c.k,104857643055355+c.lower,104858026168821+c.upper)) = pointBounds29140 := by
 decide +kernel
def cuts29141 : List PrefixCut := [⟨114,388544879,388545100⟩,
⟨128,436909715,436909961⟩]
theorem checked29141 : checkPrefixCuts (2^48) 3823501313 9 Manual.Count131072.C029141.packed 128 cuts29141 = true := by
 decide +kernel
def pointBounds29141 : List (Nat × Nat × Nat) := [(3823618048,104858460721346,104858843835275)]
theorem point_links_checked29141 : (cuts29141.take 1).map (fun c => (3823501313-1+2*2^9*c.k,104858072176467+c.lower,104858455290175+c.upper)) = pointBounds29141 := by
 decide +kernel
def cuts29142 : List PrefixCut := [⟨103,352387829,352388028⟩,
⟨128,437041922,437042170⟩]
theorem checked29142 : checkPrefixCuts (2^48) 3823632385 9 Manual.Count131072.C029142.packed 128 cuts29142 = true := by
 decide +kernel
def pointBounds29142 : List (Nat × Nat × Nat) := [(3823737856,104858861474011,104859244588164)]
theorem point_links_checked29142 : (cuts29142.take 1).map (fun c => (3823632385-1+2*2^9*c.k,104858509086182+c.lower,104858892200136+c.upper)) = pointBounds29142 := by
 decide +kernel
def cuts29143 : List PrefixCut := [⟨92,322342971,322343146⟩,
⟨128,441517290,441517533⟩]
theorem checked29143 : checkPrefixCuts (2^48) 3823763457 9 Manual.Count131072.C029143.packed 128 cuts29143 = true := by
 decide +kernel
def pointBounds29143 : List (Nat × Nat × Nat) := [(3823857664,104859268471075,104859651585452)]
theorem point_links_checked29143 : (cuts29143.take 1).map (fun c => (3823763457-1+2*2^9*c.k,104858946128104+c.lower,104859329242306+c.upper)) = pointBounds29143 := by
 decide +kernel
def cuts29144 : List PrefixCut := [⟨81,273235416,273235573⟩,
⟨128,434141240,434141489⟩]
theorem checked29144 : checkPrefixCuts (2^48) 3823894529 9 Manual.Count131072.C029144.packed 128 cuts29144 = true := by
 decide +kernel
def pointBounds29144 : List (Nat × Nat × Nat) := [(3823977472,104859660880810,104860043995412)]
theorem point_links_checked29144 : (cuts29144.take 1).map (fun c => (3823894529-1+2*2^9*c.k,104859387645394+c.lower,104859770759839+c.upper)) = pointBounds29144 := by
 decide +kernel
def cuts29145 : List PrefixCut := [⟨70,237969072,237969211⟩,
⟨128,436040131,436040384⟩]
theorem checked29145 : checkPrefixCuts (2^48) 3824025601 9 Manual.Count131072.C029145.packed 128 cuts29145 = true := by
 decide +kernel
def pointBounds29145 : List (Nat × Nat × Nat) := [(3824097280,104860059755706,104860442870539)]
theorem point_links_checked29145 : (cuts29145.take 1).map (fun c => (3824025601-1+2*2^9*c.k,104859821786634+c.lower,104860204901328+c.upper)) = pointBounds29145 := by
 decide +kernel
def cuts29146 : List PrefixCut := [⟨59,200423301,200423417⟩,
⟨128,432418692,432418936⟩]
theorem checked29146 : checkPrefixCuts (2^48) 3824156673 9 Manual.Count131072.C029146.packed 128 cuts29146 = true := by
 decide +kernel
def pointBounds29146 : List (Nat × Nat × Nat) := [(3824217088,104860458250066,104860841365129)]
theorem point_links_checked29146 : (cuts29146.take 1).map (fun c => (3824156673-1+2*2^9*c.k,104860257826765+c.lower,104860640941712+c.upper)) = pointBounds29146 := by
 decide +kernel
def cuts29147 : List PrefixCut := [⟨48,160598343,160598435⟩,
⟨128,434023000,434023244⟩]
theorem checked29147 : checkPrefixCuts (2^48) 3824287745 9 Manual.Count131072.C029147.packed 128 cuts29147 = true := by
 decide +kernel
def pointBounds29147 : List (Nat × Nat × Nat) := [(3824336896,104860850843800,104861233959083)]
theorem point_links_checked29147 : (cuts29147.take 1).map (fun c => (3824287745-1+2*2^9*c.k,104860690245457+c.lower,104861073360648+c.upper)) = pointBounds29147 := by
 decide +kernel
def cuts29148 : List PrefixCut := [⟨37,124823954,124824024⟩,
⟨128,434523381,434523628⟩]
theorem checked29148 : checkPrefixCuts (2^48) 3824418817 9 Manual.Count131072.C029148.packed 128 cuts29148 = true := by
 decide +kernel
def pointBounds29148 : List (Nat × Nat × Nat) := [(3824456704,104861249092411,104861632207916)]
theorem point_links_checked29148 : (cuts29148.take 1).map (fun c => (3824418817-1+2*2^9*c.k,104861124268457+c.lower,104861507383892+c.upper)) = pointBounds29148 := by
 decide +kernel
def cuts29149 : List PrefixCut := [⟨26,87874362,87874410⟩,
⟨128,437893856,437894101⟩]
theorem checked29149 : checkPrefixCuts (2^48) 3824549889 9 Manual.Count131072.C029149.packed 128 cuts29149 = true := by
 decide +kernel
def pointBounds29149 : List (Nat × Nat × Nat) := [(3824576512,104861646666200,104862029781930)]
theorem point_links_checked29149 : (cuts29149.take 1).map (fun c => (3824549889-1+2*2^9*c.k,104861558791838+c.lower,104861941907520+c.upper)) = pointBounds29149 := by
 decide +kernel
def cuts29150 : List PrefixCut := [⟨15,52619850,52619880⟩,
⟨128,438614785,438615031⟩]
theorem checked29150 : checkPrefixCuts (2^48) 3824680961 9 Manual.Count131072.C029150.packed 128 cuts29150 = true := by
 decide +kernel
def pointBounds29150 : List (Nat × Nat × Nat) := [(3824696320,104862049305544,104862432421501)]
theorem point_links_checked29150 : (cuts29150.take 1).map (fun c => (3824680961-1+2*2^9*c.k,104861996685694+c.lower,104862379801621+c.upper)) = pointBounds29150 := by
 decide +kernel
def cuts29151 : List PrefixCut := [⟨4,14056031,14056038⟩,
⟨121,415934318,415934558⟩,
⟨128,442352902,442353157⟩]
theorem checked29151 : checkPrefixCuts (2^48) 3824812033 9 Manual.Count131072.C029151.packed 128 cuts29151 = true := by
 decide +kernel
def pointBounds29151 : List (Nat × Nat × Nat) := [(3824816128,104862449356510,104862832472690),(3824935936,104862851234797,104863234351210)]
theorem point_links_checked29151 : (cuts29151.take 2).map (fun c => (3824812033-1+2*2^9*c.k,104862435300479+c.lower,104862818416652+c.upper)) = pointBounds29151 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000285
