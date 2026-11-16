import PlattAssemblyKernel
import PlattCertificates.Count131072.C015120
import PlattCertificates.Count131072.C015121
import PlattCertificates.Count131072.C015122
import PlattCertificates.Count131072.C015123
import PlattCertificates.Count131072.C015124
import PlattCertificates.Count131072.C015125
import PlattCertificates.Count131072.C015126
import PlattCertificates.Count131072.C015127
import PlattCertificates.Count131072.C015128
import PlattCertificates.Count131072.C015129
import PlattCertificates.Count131072.C015130
import PlattCertificates.Count131072.C015131
import PlattCertificates.Count131072.C015132
import PlattCertificates.Count131072.C015133
import PlattCertificates.Count131072.C015134
import PlattCertificates.Count131072.C015135
import PlattCertificates.Count131072.C015136
import PlattCertificates.Count131072.C015137
import PlattCertificates.Count131072.C015138
import PlattCertificates.Count131072.C015139
import PlattCertificates.Count131072.C015140
import PlattCertificates.Count131072.C015141
import PlattCertificates.Count131072.C015142
import PlattCertificates.Count131072.C015143
import PlattCertificates.Count131072.C015144
import PlattCertificates.Count131072.C015145
import PlattCertificates.Count131072.C015146
import PlattCertificates.Count131072.C015147
import PlattCertificates.Count131072.C015148
import PlattCertificates.Count131072.C015149
import PlattCertificates.Count131072.C015150
import PlattCertificates.Count131072.C015151
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000160
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts15120 : List PrefixCut := [⟨32,205674722,205674856⟩,
⟨93,614179327,614179731⟩,
⟨128,852586000,852586561⟩]
theorem checked15120 : checkPrefixCuts (2^48) 1985740801 9 Manual.Count131072.C015120.packed 128 cuts15120 = true := by
 decide +kernel
def pointBounds15120 : List (Nat × Nat × Nat) := [(1985773568,96373577253198,96373955356733),(1985836032,96373985757803,96374363861608)]
theorem point_links_checked15120 : (cuts15120.take 2).map (fun c => (1985740801-1+2*2^9*c.k,96373371578476+c.lower,96373749681877+c.upper)) = pointBounds15120 := by
 decide +kernel
def cuts15121 : List PrefixCut := [⟨26,179723437,179723558⟩,
⟨87,591462348,591462746⟩,
⟨128,868546165,868546751⟩]
theorem checked15121 : checkPrefixCuts (2^48) 1985871873 9 Manual.Count131072.C015121.packed 128 cuts15121 = true := by
 decide +kernel
def pointBounds15121 : List (Nat × Nat × Nat) := [(1985898496,96374403887913,96374781991996),(1985960960,96374815626824,96375193731184)]
theorem point_links_checked15121 : (cuts15121.take 2).map (fun c => (1985871873-1+2*2^9*c.k,96374224164476+c.lower,96374602268438+c.upper)) = pointBounds15121 := by
 decide +kernel
def cuts15122 : List PrefixCut := [⟨20,132799711,132799801⟩,
⟨81,553866535,553866900⟩,
⟨128,873590660,873591237⟩]
theorem checked15122 : checkPrefixCuts (2^48) 1986002945 9 Manual.Count131072.C015122.packed 128 cuts15122 = true := by
 decide +kernel
def pointBounds15122 : List (Nat × Nat × Nat) := [(1986023424,96375225510352,96375603614990),(1986085888,96375646577176,96376024682089)]
theorem point_links_checked15122 : (cuts15122.take 2).map (fun c => (1986002945-1+2*2^9*c.k,96375092710641+c.lower,96375470815189+c.upper)) = pointBounds15122 := by
 decide +kernel
def cuts15123 : List PrefixCut := [⟨14,94952050,94952114⟩,
⟨75,503096208,503096543⟩,
⟨128,864038109,864038685⟩]
theorem checked15123 : checkPrefixCuts (2^48) 1986134017 9 Manual.Count131072.C015123.packed 128 cuts15123 = true := by
 decide +kernel
def pointBounds15123 : List (Nat × Nat × Nat) := [(1986148352,96376061253351,96376439358540),(1986210816,96376469397509,96376847502969)]
theorem point_links_checked15123 : (cuts15123.take 2).map (fun c => (1986134017-1+2*2^9*c.k,96375966301301+c.lower,96376344406426+c.upper)) = pointBounds15123 := by
 decide +kernel
def cuts15124 : List PrefixCut := [⟨8,53424797,53424832⟩,
⟨69,468203532,468203843⟩,
⟨128,868232237,868232819⟩]
theorem checked15124 : checkPrefixCuts (2^48) 1986265089 9 Manual.Count131072.C015124.packed 128 cuts15124 = true := by
 decide +kernel
def pointBounds15124 : List (Nat × Nat × Nat) := [(1986273280,96376883764207,96377261869943),(1986335744,96377298542942,96377676648954)]
theorem point_links_checked15124 : (cuts15124.take 2).map (fun c => (1986265089-1+2*2^9*c.k,96376830339410+c.lower,96377208445111+c.upper)) = pointBounds15124 := by
 decide +kernel
def cuts15125 : List PrefixCut := [⟨2,14311823,14311832⟩,
⟨63,426088833,426089116⟩,
⟨124,841111847,841112406⟩,
⟨128,868033345,868033921⟩]
theorem checked15125 : checkPrefixCuts (2^48) 1986396161 9 Manual.Count131072.C015125.packed 128 cuts15125 = true := by
 decide +kernel
def pointBounds15125 : List (Nat × Nat × Nat) := [(1986398208,96377712883470,96378090989762),(1986460672,96378124660480,96378502767046),(1986523136,96378539683494,96378917790336)]
theorem point_links_checked15125 : (cuts15125.take 3).map (fun c => (1986396161-1+2*2^9*c.k,96377698571647+c.lower,96378076677930+c.upper)) = pointBounds15125 := by
 decide +kernel
def cuts15126 : List PrefixCut := [⟨57,380153799,380154050⟩,
⟨118,794867441,794867961⟩,
⟨128,859474867,859475431⟩]
theorem checked15126 : checkPrefixCuts (2^48) 1986527233 9 Manual.Count131072.C015126.packed 128 cuts15126 = true := by
 decide +kernel
def pointBounds15126 : List (Nat × Nat × Nat) := [(1986585600,96378946758791,96379324865901),(1986648064,96379361472433,96379739579812)]
theorem point_links_checked15126 : (cuts15126.take 2).map (fun c => (1986527233-1+2*2^9*c.k,96378566604992+c.lower,96378944711851+c.upper)) = pointBounds15126 := by
 decide +kernel
def cuts15127 : List PrefixCut := [⟨51,352643369,352643603⟩,
⟨112,764497241,764497749⟩,
⟨128,873727753,873728331⟩]
theorem checked15127 : checkPrefixCuts (2^48) 1986658305 9 Manual.Count131072.C015127.packed 128 cuts15127 = true := by
 decide +kernel
def pointBounds15127 : List (Nat × Nat × Nat) := [(1986710528,96379778723228,96380156830885),(1986772992,96380190577100,96380568685031)]
theorem point_links_checked15127 : (cuts15127.take 2).map (fun c => (1986658305-1+2*2^9*c.k,96379426079859+c.lower,96379804187282+c.upper)) = pointBounds15127 := by
 decide +kernel
def cuts15128 : List PrefixCut := [⟨45,307852370,307852571⟩,
⟨106,730447161,730447638⟩,
⟨128,879195109,879195684⟩]
theorem checked15128 : checkPrefixCuts (2^48) 1986789377 9 Manual.Count131072.C015128.packed 128 cuts15128 = true := by
 decide +kernel
def pointBounds15128 : List (Nat × Nat × Nat) := [(1986835456,96380607659982,96380985768184),(1986897920,96381030254773,96381408363251)]
theorem point_links_checked15128 : (cuts15128.take 2).map (fun c => (1986789377-1+2*2^9*c.k,96380299807612+c.lower,96380677915613+c.upper)) = pointBounds15128 := by
 decide +kernel
def cuts15129 : List PrefixCut := [⟨39,263067173,263067349⟩,
⟨100,679402503,679402959⟩,
⟨128,872195744,872196329⟩]
theorem checked15129 : checkPrefixCuts (2^48) 1986920449 9 Manual.Count131072.C015129.packed 128 cuts15129 = true := by
 decide +kernel
def pointBounds15129 : List (Nat × Nat × Nat) := [(1986960384,96381442069894,96381820178646),(1987022848,96381858405224,96382236514256)]
theorem point_links_checked15129 : (cuts15129.take 2).map (fun c => (1986920449-1+2*2^9*c.k,96381179002721+c.lower,96381557111297+c.upper)) = pointBounds15129 := by
 decide +kernel
def cuts15130 : List PrefixCut := [⟨33,225653786,225653936⟩,
⟨94,633038902,633039320⟩,
⟨128,861939561,861940132⟩]
theorem checked15130 : checkPrefixCuts (2^48) 1987051521 9 Manual.Count131072.C015130.packed 128 cuts15130 = true := by
 decide +kernel
def pointBounds15130 : List (Nat × Nat × Nat) := [(1987085312,96382276852251,96382654961562),(1987147776,96382684237367,96383062346946)]
theorem point_links_checked15130 : (cuts15130.take 2).map (fun c => (1987051521-1+2*2^9*c.k,96382051198465+c.lower,96382429307626+c.upper)) = pointBounds15130 := by
 decide +kernel
def cuts15131 : List PrefixCut := [⟨27,181446256,181446379⟩,
⟨88,594329831,594330229⟩,
⟨128,858766714,858767292⟩]
theorem checked15131 : checkPrefixCuts (2^48) 1987182593 9 Manual.Count131072.C015131.packed 128 cuts15131 = true := by
 decide +kernel
def pointBounds15131 : List (Nat × Nat × Nat) := [(1987210240,96383094584282,96383472694137),(1987272704,96383507467857,96383885577987)]
theorem point_links_checked15131 : (cuts15131.take 2).map (fun c => (1987182593-1+2*2^9*c.k,96382913138026+c.lower,96383291247758+c.upper)) = pointBounds15131 := by
 decide +kernel
def cuts15132 : List PrefixCut := [⟨21,139793837,139793930⟩,
⟨82,550668541,550668905⟩,
⟨128,869473652,869474225⟩]
theorem checked15132 : checkPrefixCuts (2^48) 1987313665 9 Manual.Count131072.C015132.packed 128 cuts15132 = true := by
 decide +kernel
def pointBounds15132 : List (Nat × Nat × Nat) := [(1987335168,96383911698577,96384289808980),(1987397632,96384322573281,96384700683955)]
theorem point_links_checked15132 : (cuts15132.take 2).map (fun c => (1987313665-1+2*2^9*c.k,96383771904740+c.lower,96384150015050+c.upper)) = pointBounds15132 := by
 decide +kernel
def cuts15133 : List PrefixCut := [⟨15,102395579,102395648⟩,
⟨76,512536402,512536743⟩,
⟨128,858936614,858937182⟩]
theorem checked15133 : checkPrefixCuts (2^48) 1987444737 9 Manual.Count131072.C015133.packed 128 cuts15133 = true := by
 decide +kernel
def pointBounds15133 : List (Nat × Nat × Nat) := [(1987460096,96384743773971,96385121884923),(1987522560,96385153914794,96385532026018)]
theorem point_links_checked15133 : (cuts15133.take 2).map (fun c => (1987444737-1+2*2^9*c.k,96384641378392+c.lower,96385019489275+c.upper)) = pointBounds15133 := by
 decide +kernel
def cuts15134 : List PrefixCut := [⟨9,61178480,61178521⟩,
⟨70,476533275,476533593⟩,
⟨128,867093561,867094133⟩]
theorem checked15134 : checkPrefixCuts (2^48) 1987575809 9 Manual.Count131072.C015134.packed 128 cuts15134 = true := by
 decide +kernel
def pointBounds15134 : List (Nat × Nat × Nat) := [(1987585024,96385561493486,96385939604978),(1987647488,96385976848281,96386354960050)]
theorem point_links_checked15134 : (cuts15134.take 2).map (fun c => (1987575809-1+2*2^9*c.k,96385500315006+c.lower,96385878426457+c.upper)) = pointBounds15134 := by
 decide +kernel
def cuts15135 : List PrefixCut := [⟨3,17842574,17842586⟩,
⟨64,433454454,433454740⟩,
⟨125,864912517,864913090⟩,
⟨128,883178737,883179324⟩]
theorem checked15135 : checkPrefixCuts (2^48) 1987706881 9 Manual.Count131072.C015135.packed 128 cuts15135 = true := by
 decide +kernel
def pointBounds15135 : List (Nat × Nat × Nat) := [(1987709952,96386385251141,96386763363176),(1987772416,96386800863021,96387178975330),(1987834880,96387232321084,96387610433680)]
theorem point_links_checked15135 : (cuts15135.take 3).map (fun c => (1987706881-1+2*2^9*c.k,96386367408567+c.lower,96386745520590+c.upper)) = pointBounds15135 := by
 decide +kernel
def cuts15136 : List PrefixCut := [⟨58,385425310,385425568⟩,
⟨119,798874139,798874677⟩,
⟨128,858341726,858342303⟩]
theorem checked15136 : checkPrefixCuts (2^48) 1987837953 9 Manual.Count131072.C015136.packed 128 cuts15136 = true := by
 decide +kernel
def pointBounds15136 : List (Nat × Nat × Nat) := [(1987897344,96387636012614,96388014125482),(1987959808,96388049461443,96388427574591)]
theorem point_links_checked15136 : (cuts15136.take 2).map (fun c => (1987837953-1+2*2^9*c.k,96387250587304+c.lower,96387628699914+c.upper)) = pointBounds15136 := by
 decide +kernel
def cuts15137 : List PrefixCut := [⟨52,364162456,364162696⟩,
⟨113,767391244,767391751⟩,
⟨128,871169652,871170228⟩]
theorem checked15137 : checkPrefixCuts (2^48) 1987969025 9 Manual.Count131072.C015137.packed 128 cuts15137 = true := by
 decide +kernel
def pointBounds15137 : List (Nat × Nat × Nat) := [(1988022272,96388473091486,96388851204913),(1988084736,96388876320274,96389254433968)]
theorem point_links_checked15137 : (cuts15137.take 2).map (fun c => (1987969025-1+2*2^9*c.k,96388108929030+c.lower,96388487042217+c.upper)) = pointBounds15137 := by
 decide +kernel
def cuts15138 : List PrefixCut := [⟨46,308215666,308215872⟩,
⟨107,714109030,714109504⟩,
⟨128,859502733,859503304⟩]
theorem checked15138 : checkPrefixCuts (2^48) 1988100097 9 Manual.Count131072.C015138.packed 128 cuts15138 = true := by
 decide +kernel
def pointBounds15138 : List (Nat × Nat × Nat) := [(1988147200,96389288314348,96389666428317),(1988209664,96389694207712,96390072321949)]
theorem point_links_checked15138 : (cuts15138.take 2).map (fun c => (1988100097-1+2*2^9*c.k,96388980098682+c.lower,96389358212445+c.upper)) = pointBounds15138 := by
 decide +kernel
def cuts15139 : List PrefixCut := [⟨40,267990201,267990379⟩,
⟨101,679945462,679945914⟩,
⟨128,858455329,858455898⟩]
theorem checked15139 : checkPrefixCuts (2^48) 1988231169 9 Manual.Count131072.C015139.packed 128 cuts15139 = true := by
 decide +kernel
def pointBounds15139 : List (Nat × Nat × Nat) := [(1988272128,96390107591616,96390485706128),(1988334592,96390519546877,96390897661663)]
theorem point_links_checked15139 : (cuts15139.take 2).map (fun c => (1988231169-1+2*2^9*c.k,96389839601415+c.lower,96390217715749+c.upper)) = pointBounds15139 := by
 decide +kernel
def cuts15140 : List PrefixCut := [⟨34,235272655,235272810⟩,
⟨95,644229299,644229727⟩,
⟨128,865618243,865618819⟩]
theorem checked15140 : checkPrefixCuts (2^48) 1988362241 9 Manual.Count131072.C015140.packed 128 cuts15140 = true := by
 decide +kernel
def pointBounds15140 : List (Nat × Nat × Nat) := [(1988397056,96390933329399,96391311444457),(1988459520,96391342286043,96391720401374)]
theorem point_links_checked15140 : (cuts15140.take 2).map (fun c => (1988362241-1+2*2^9*c.k,96390698056744+c.lower,96391076171647+c.upper)) = pointBounds15140 := by
 decide +kernel
def cuts15141 : List PrefixCut := [⟨28,191376727,191376852⟩,
⟨89,605120238,605120633⟩,
⟨128,873345986,873346558⟩]
theorem checked15141 : checkPrefixCuts (2^48) 1988493313 9 Manual.Count131072.C015141.packed 128 cuts15141 = true := by
 decide +kernel
def pointBounds15141 : List (Nat × Nat × Nat) := [(1988521984,96391755051714,96392133167318),(1988584448,96392168795225,96392546911099)]
theorem point_links_checked15141 : (cuts15141.take 2).map (fun c => (1988493313-1+2*2^9*c.k,96391563674987+c.lower,96391941790466+c.upper)) = pointBounds15141 := by
 decide +kernel
def cuts15142 : List PrefixCut := [⟨22,145787961,145788060⟩,
⟨83,562477849,562478219⟩,
⟨128,872439118,872439687⟩]
theorem checked15142 : checkPrefixCuts (2^48) 1988624385 9 Manual.Count131072.C015142.packed 128 cuts15142 = true := by
 decide +kernel
def pointBounds15142 : List (Nat × Nat × Nat) := [(1988646912,96392582808934,96392960925084),(1988709376,96392999498822,96393377615243)]
theorem point_links_checked15142 : (cuts15142.take 2).map (fun c => (1988624385-1+2*2^9*c.k,96392437020973+c.lower,96392815137024+c.upper)) = pointBounds15142 := by
 decide +kernel
def cuts15143 : List PrefixCut := [⟨16,105866373,105866444⟩,
⟨77,524936098,524936449⟩,
⟨128,871957125,871957708⟩]
theorem checked15143 : checkPrefixCuts (2^48) 1988755457 9 Manual.Count131072.C015143.packed 128 cuts15143 = true := by
 decide +kernel
def pointBounds15143 : List (Nat × Nat × Nat) := [(1988771840,96393415326464,96393793443155),(1988834304,96393834396189,96394212513160)]
theorem point_links_checked15143 : (cuts15143.take 2).map (fun c => (1988755457-1+2*2^9*c.k,96393309460091+c.lower,96393687576711+c.upper)) = pointBounds15143 := by
 decide +kernel
def cuts15144 : List PrefixCut := [⟨10,68780416,68780462⟩,
⟨71,483436698,483437017⟩,
⟨128,869352417,869352995⟩]
theorem checked15144 : checkPrefixCuts (2^48) 1988886529 9 Manual.Count131072.C015144.packed 128 cuts15144 = true := by
 decide +kernel
def pointBounds15144 : List (Nat × Nat × Nat) := [(1988896768,96394250197632,96394628314881),(1988959232,96394664853914,96395042971436)]
theorem point_links_checked15144 : (cuts15144.take 2).map (fun c => (1988886529-1+2*2^9*c.k,96394181417216+c.lower,96394559534419+c.upper)) = pointBounds15144 := by
 decide +kernel
def cuts15145 : List PrefixCut := [⟨4,25048045,25048062⟩,
⟨65,434017846,434018135⟩,
⟨126,844672836,844673397⟩,
⟨128,858257342,858257912⟩]
theorem checked15145 : checkPrefixCuts (2^48) 1989017601 9 Manual.Count131072.C015145.packed 128 cuts15145 = true := by
 decide +kernel
def pointBounds15145 : List (Nat × Nat × Nat) := [(1989021696,96395075817678,96395453935476),(1989084160,96395484787479,96395862905549),(1989146624,96395895442469,96396273560811)]
theorem point_links_checked15145 : (cuts15145.take 3).map (fun c => (1989017601-1+2*2^9*c.k,96395050769633+c.lower,96395428887414+c.upper)) = pointBounds15145 := by
 decide +kernel
def cuts15146 : List PrefixCut := [⟨59,397765069,397765336⟩,
⟨120,816318185,816318727⟩,
⟨128,868530274,868530851⟩]
theorem checked15146 : checkPrefixCuts (2^48) 1989148673 9 Manual.Count131072.C015146.packed 128 cuts15146 = true := by
 decide +kernel
def pointBounds15146 : List (Nat × Nat × Nat) := [(1989209088,96396306792044,96396684910662),(1989271552,96396725345160,96397103464053)]
theorem point_links_checked15146 : (cuts15146.take 2).map (fun c => (1989148673-1+2*2^9*c.k,96395909026975+c.lower,96396287145326+c.upper)) = pointBounds15146 := by
 decide +kernel
def cuts15147 : List PrefixCut := [⟨53,356706265,356706514⟩,
⟨114,772686184,772686705⟩,
⟨128,865643184,865643769⟩]
theorem checked15147 : checkPrefixCuts (2^48) 1989279745 9 Manual.Count131072.C015147.packed 128 cuts15147 = true := by
 decide +kernel
def pointBounds15147 : List (Nat × Nat × Nat) := [(1989334016,96397134263514,96397512382691),(1989396480,96397550243433,96397928362882)]
theorem point_links_checked15147 : (cuts15147.take 2).map (fun c => (1989279745-1+2*2^9*c.k,96396777557249+c.lower,96397155676177+c.upper)) = pointBounds15147 := by
 decide +kernel
def cuts15148 : List PrefixCut := [⟨47,321453578,321453786⟩,
⟨108,731889679,731890161⟩,
⟨128,867708503,867709079⟩]
theorem checked15148 : checkPrefixCuts (2^48) 1989410817 9 Manual.Count131072.C015148.packed 128 cuts15148 = true := by
 decide +kernel
def pointBounds15148 : List (Nat × Nat × Nat) := [(1989458944,96397964654011,96398342773732),(1989521408,96398375090112,96398753210107)]
theorem point_links_checked15148 : (cuts15148.take 2).map (fun c => (1989410817-1+2*2^9*c.k,96397643200433+c.lower,96398021319946+c.upper)) = pointBounds15148 := by
 decide +kernel
def cuts15149 : List PrefixCut := [⟨41,277433866,277434046⟩,
⟨102,685439215,685439668⟩,
⟨128,863407036,863407608⟩]
theorem checked15149 : checkPrefixCuts (2^48) 1989541889 9 Manual.Count131072.C015149.packed 128 cuts15149 = true := by
 decide +kernel
def pointBounds15149 : List (Nat × Nat × Nat) := [(1989583872,96398788342802,96399166463071),(1989646336,96399196348151,96399574468693)]
theorem point_links_checked15149 : (cuts15149.take 2).map (fun c => (1989541889-1+2*2^9*c.k,96398510908936+c.lower,96398889029025+c.upper)) = pointBounds15149 := by
 decide +kernel
def cuts15150 : List PrefixCut := [⟨35,238654244,238654403⟩,
⟨96,653848622,653849054⟩,
⟨128,874384384,874384960⟩]
theorem checked15150 : checkPrefixCuts (2^48) 1989672961 9 Manual.Count131072.C015150.packed 128 cuts15150 = true := by
 decide +kernel
def pointBounds15150 : List (Nat × Nat × Nat) := [(1989708800,96399612970216,96399991091036),(1989771264,96400028164594,96400406285687)]
theorem point_links_checked15150 : (cuts15150.take 2).map (fun c => (1989672961-1+2*2^9*c.k,96399374315972+c.lower,96399752436633+c.upper)) = pointBounds15150 := by
 decide +kernel
def cuts15151 : List PrefixCut := [⟨29,195069959,195070092⟩,
⟨90,602033940,602034348⟩,
⟨128,855796425,855797000⟩]
theorem checked15151 : checkPrefixCuts (2^48) 1989804033 9 Manual.Count131072.C015151.packed 128 cuts15151 = true := by
 decide +kernel
def pointBounds15151 : List (Nat × Nat × Nat) := [(1989833728,96400443770315,96400821891685),(1989896192,96400850734296,96401228855941)]
theorem point_links_checked15151 : (cuts15151.take 2).map (fun c => (1989804033-1+2*2^9*c.k,96400248700356+c.lower,96400626821593+c.upper)) = pointBounds15151 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000160
