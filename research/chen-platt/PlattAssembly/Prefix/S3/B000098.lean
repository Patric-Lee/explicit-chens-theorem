import PlattAssemblyKernel
import PlattCertificates.Count131072.C023136
import PlattCertificates.Count131072.C023137
import PlattCertificates.Count131072.C023138
import PlattCertificates.Count131072.C023139
import PlattCertificates.Count131072.C023140
import PlattCertificates.Count131072.C023141
import PlattCertificates.Count131072.C023142
import PlattCertificates.Count131072.C023143
import PlattCertificates.Count131072.C023144
import PlattCertificates.Count131072.C023145
import PlattCertificates.Count131072.C023146
import PlattCertificates.Count131072.C023147
import PlattCertificates.Count131072.C023148
import PlattCertificates.Count131072.C023149
import PlattCertificates.Count131072.C023150
import PlattCertificates.Count131072.C023151
import PlattCertificates.Count131072.C023152
import PlattCertificates.Count131072.C023153
import PlattCertificates.Count131072.C023154
import PlattCertificates.Count131072.C023155
import PlattCertificates.Count131072.C023156
import PlattCertificates.Count131072.C023157
import PlattCertificates.Count131072.C023158
import PlattCertificates.Count131072.C023159
import PlattCertificates.Count131072.C023160
import PlattCertificates.Count131072.C023161
import PlattCertificates.Count131072.C023162
import PlattCertificates.Count131072.C023163
import PlattCertificates.Count131072.C023164
import PlattCertificates.Count131072.C023165
import PlattCertificates.Count131072.C023166
import PlattCertificates.Count131072.C023167
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000098
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts23136 : List PrefixCut := [⟨52,225258497,225258629⟩,
⟨128,557577085,557577408⟩]
theorem checked23136 : checkPrefixCuts (2^48) 3036413953 9 Manual.Count131072.C023136.packed 128 cuts23136 = true := by
 decide +kernel
def pointBounds23136 : List (Nat × Nat × Nat) := [(3036467200,101902334126993,101902715581583)]
theorem point_links_checked23136 : (cuts23136.take 1).map (fun c => (3036413953-1+2*2^9*c.k,101902108868496+c.lower,101902490322954+c.upper)) = pointBounds23136 := by
 decide +kernel
def cuts23137 : List PrefixCut := [⟨17,73971019,73971061⟩,
⟨110,480711393,480711669⟩,
⟨128,557738493,557738814⟩]
theorem checked23137 : checkPrefixCuts (2^48) 3036545025 9 Manual.Count131072.C023137.packed 128 cuts23137 = true := by
 decide +kernel
def pointBounds23137 : List (Nat × Nat × Nat) := [(3036562432,101902740416600,101903121871423),(3036657664,101903147156974,101903528612031)]
theorem point_links_checked23137 : (cuts23137.take 2).map (fun c => (3036545025-1+2*2^9*c.k,101902666445581+c.lower,101903047900362+c.upper)) = pointBounds23137 := by
 decide +kernel
def cuts23138 : List PrefixCut := [⟨75,328588192,328588375⟩,
⟨128,561792711,561793024⟩]
theorem checked23138 : checkPrefixCuts (2^48) 3036676097 9 Manual.Count131072.C023138.packed 128 cuts23138 = true := by
 decide +kernel
def pointBounds23138 : List (Nat × Nat × Nat) := [(3036752896,101903552772266,101903934227551)]
theorem point_links_checked23138 : (cuts23138.take 1).map (fun c => (3036676097-1+2*2^9*c.k,101903224184074+c.lower,101903605639176+c.upper)) = pointBounds23138 := by
 decide +kernel
def cuts23139 : List PrefixCut := [⟨40,173695705,173695806⟩,
⟨128,560378173,560378493⟩]
theorem checked23139 : checkPrefixCuts (2^48) 3036807169 9 Manual.Count131072.C023139.packed 128 cuts23139 = true := by
 decide +kernel
def pointBounds23139 : List (Nat × Nat × Nat) := [(3036848128,101903959672490,101904341128006)]
theorem point_links_checked23139 : (cuts23139.take 1).map (fun c => (3036807169-1+2*2^9*c.k,101903785976785+c.lower,101904167432200+c.upper)) = pointBounds23139 := by
 decide +kernel
def cuts23140 : List PrefixCut := [⟨5,22336771,22336784⟩,
⟨98,430416350,430416594⟩,
⟨128,559149216,559149533⟩]
theorem checked23140 : checkPrefixCuts (2^48) 3036938241 9 Manual.Count131072.C023140.packed 128 cuts23140 = true := by
 decide +kernel
def pointBounds23140 : List (Nat × Nat × Nat) := [(3036943360,101904368691729,101904750147477),(3037038592,101904776771308,101905158227287)]
theorem point_links_checked23140 : (cuts23140.take 2).map (fun c => (3036938241-1+2*2^9*c.k,101904346354958+c.lower,101904727810693+c.upper)) = pointBounds23140 := by
 decide +kernel
def cuts23141 : List PrefixCut := [⟨63,274699949,274700098⟩,
⟨128,559866418,559866731⟩]
theorem checked23141 : checkPrefixCuts (2^48) 3037069313 9 Manual.Count131072.C023141.packed 128 cuts23141 = true := by
 decide +kernel
def pointBounds23141 : List (Nat × Nat × Nat) := [(3037133824,101905180204123,101905561660324)]
theorem point_links_checked23141 : (cuts23141.take 1).map (fun c => (3037069313-1+2*2^9*c.k,101904905504174+c.lower,101905286960226+c.upper)) = pointBounds23141 := by
 decide +kernel
def cuts23142 : List PrefixCut := [⟨28,119551184,119551254⟩,
⟨121,521105209,521105509⟩,
⟨128,552242962,552243283⟩]
theorem checked23142 : checkPrefixCuts (2^48) 3037200385 9 Manual.Count131072.C023142.packed 128 cuts23142 = true := by
 decide +kernel
def pointBounds23142 : List (Nat × Nat × Nat) := [(3037229056,101905584921776,101905966378211),(3037324288,101905986475801,101906367932466)]
theorem point_links_checked23142 : (cuts23142.take 2).map (fun c => (3037200385-1+2*2^9*c.k,101905465370592+c.lower,101905846826957+c.upper)) = pointBounds23142 := by
 decide +kernel
def cuts23143 : List PrefixCut := [⟨86,375037205,375037424⟩,
⟨128,556018656,556018975⟩]
theorem checked23143 : checkPrefixCuts (2^48) 3037331457 9 Manual.Count131072.C023143.packed 128 cuts23143 = true := by
 decide +kernel
def pointBounds23143 : List (Nat × Nat × Nat) := [(3037419520,101906392650759,101906774107664)]
theorem point_links_checked23143 : (cuts23143.take 1).map (fun c => (3037331457-1+2*2^9*c.k,101906017613554+c.lower,101906399070240+c.upper)) = pointBounds23143 := by
 decide +kernel
def cuts23144 : List PrefixCut := [⟨51,223976080,223976208⟩,
⟨128,559701293,559701611⟩]
theorem checked23144 : checkPrefixCuts (2^48) 3037462529 9 Manual.Count131072.C023144.packed 128 cuts23144 = true := by
 decide +kernel
def pointBounds23144 : List (Nat × Nat × Nat) := [(3037514752,101906797608290,101907179065423)]
theorem point_links_checked23144 : (cuts23144.take 1).map (fun c => (3037462529-1+2*2^9*c.k,101906573632210+c.lower,101906955089215+c.upper)) = pointBounds23144 := by
 decide +kernel
def cuts23145 : List PrefixCut := [⟨16,67181062,67181100⟩,
⟨109,471279323,471279587⟩,
⟨128,553005512,553005821⟩]
theorem checked23145 : checkPrefixCuts (2^48) 3037593601 9 Manual.Count131072.C023145.packed 128 cuts23145 = true := by
 decide +kernel
def pointBounds23145 : List (Nat × Nat × Nat) := [(3037609984,101907200514565,101907581971926),(3037705216,101907604612826,101907986070413)]
theorem point_links_checked23145 : (cuts23145.take 2).map (fun c => (3037593601-1+2*2^9*c.k,101907133333503+c.lower,101907514790826+c.upper)) = pointBounds23145 := by
 decide +kernel
def cuts23146 : List PrefixCut := [⟨74,325139070,325139252⟩,
⟨128,557151260,557151579⟩]
theorem checked23146 : checkPrefixCuts (2^48) 3037724673 9 Manual.Count131072.C023146.packed 128 cuts23146 = true := by
 decide +kernel
def pointBounds23146 : List (Nat × Nat × Nat) := [(3037800448,101908011478085,101908392935899)]
theorem point_links_checked23146 : (cuts23146.take 1).map (fun c => (3037724673-1+2*2^9*c.k,101907686339015+c.lower,101908067796647+c.upper)) = pointBounds23146 := by
 decide +kernel
def cuts23147 : List PrefixCut := [⟨39,170207544,170207638⟩,
⟨128,561667228,561667545⟩]
theorem checked23147 : checkPrefixCuts (2^48) 3037855745 9 Manual.Count131072.C023147.packed 128 cuts23147 = true := by
 decide +kernel
def pointBounds23147 : List (Nat × Nat × Nat) := [(3037895680,101908413697819,101908795155864)]
theorem point_links_checked23147 : (cuts23147.take 1).map (fun c => (3037855745-1+2*2^9*c.k,101908243490275+c.lower,101908624948226+c.upper)) = pointBounds23147 := by
 decide +kernel
def cuts23148 : List PrefixCut := [⟨4,18900951,18900962⟩,
⟨97,418408605,418408839⟩,
⟨128,553026556,553026865⟩]
theorem checked23148 : checkPrefixCuts (2^48) 3037986817 9 Manual.Count131072.C023148.packed 128 cuts23148 = true := by
 decide +kernel
def pointBounds23148 : List (Nat × Nat × Nat) := [(3037990912,101908824058454,101909205516733),(3038086144,101909223566108,101909605024610)]
theorem point_links_checked23148 : (cuts23148.take 2).map (fun c => (3037986817-1+2*2^9*c.k,101908805157503+c.lower,101909186615771+c.upper)) = pointBounds23148 := by
 decide +kernel
def cuts23149 : List PrefixCut := [⟨62,266266955,266267100⟩,
⟨128,554670290,554670602⟩]
theorem checked23149 : checkPrefixCuts (2^48) 3038117889 9 Manual.Count131072.C023149.packed 128 cuts23149 = true := by
 decide +kernel
def pointBounds23149 : List (Nat × Nat × Nat) := [(3038181376,101909624451014,101910005909736)]
theorem point_links_checked23149 : (cuts23149.take 1).map (fun c => (3038117889-1+2*2^9*c.k,101909358184059+c.lower,101909739642636+c.upper)) = pointBounds23149 := by
 decide +kernel
def cuts23150 : List PrefixCut := [⟨27,113488127,113488192⟩,
⟨120,517775603,517775901⟩,
⟨128,553812532,553812849⟩]
theorem checked23150 : checkPrefixCuts (2^48) 3038248961 9 Manual.Count131072.C023150.packed 128 cuts23150 = true := by
 decide +kernel
def pointBounds23150 : List (Nat × Nat × Nat) := [(3038276608,101910026342476,101910407801430),(3038371840,101910430629952,101910812089139)]
theorem point_links_checked23150 : (cuts23150.take 2).map (fun c => (3038248961-1+2*2^9*c.k,101909912854349+c.lower,101910294313238+c.upper)) = pointBounds23150 := by
 decide +kernel
def cuts23151 : List PrefixCut := [⟨85,369720114,369720333⟩,
⟨128,558142686,558143010⟩]
theorem checked23151 : checkPrefixCuts (2^48) 3038380033 9 Manual.Count131072.C023151.packed 128 cuts23151 = true := by
 decide +kernel
def pointBounds23151 : List (Nat × Nat × Nat) := [(3038467072,101910836386995,101911217846420)]
theorem point_links_checked23151 : (cuts23151.take 1).map (fun c => (3038380033-1+2*2^9*c.k,101910466666881+c.lower,101910848126087+c.upper)) = pointBounds23151 := by
 decide +kernel
def cuts23152 : List PrefixCut := [⟨50,221305051,221305178⟩,
⟨128,553116573,553116887⟩]
theorem checked23152 : checkPrefixCuts (2^48) 3038511105 9 Manual.Count131072.C023152.packed 128 cuts23152 = true := by
 decide +kernel
def pointBounds23152 : List (Nat × Nat × Nat) := [(3038562304,101911246114618,101911627574275)]
theorem point_links_checked23152 : (cuts23152.take 1).map (fun c => (3038511105-1+2*2^9*c.k,101911024809567+c.lower,101911406269097+c.upper)) = pointBounds23152 := by
 decide +kernel
def cuts23153 : List PrefixCut := [⟨15,68639985,68640027⟩,
⟨108,472135758,472136027⟩,
⟨128,556612600,556612919⟩]
theorem checked23153 : checkPrefixCuts (2^48) 3038642177 9 Manual.Count131072.C023153.packed 128 cuts23153 = true := by
 decide +kernel
def pointBounds23153 : List (Nat × Nat × Nat) := [(3038657536,101911646566125,101912028026011),(3038752768,101912050061898,101912431522011)]
theorem point_links_checked23153 : (cuts23153.take 2).map (fun c => (3038642177-1+2*2^9*c.k,101911577926140+c.lower,101911959385984+c.upper)) = pointBounds23153 := by
 decide +kernel
def cuts23154 : List PrefixCut := [⟨73,315301162,315301337⟩,
⟨128,551957177,551957486⟩]
theorem checked23154 : checkPrefixCuts (2^48) 3038773249 9 Manual.Count131072.C023154.packed 128 cuts23154 = true := by
 decide +kernel
def pointBounds23154 : List (Nat × Nat × Nat) := [(3038848000,101912449839902,101912831300240)]
theorem point_links_checked23154 : (cuts23154.take 1).map (fun c => (3038773249-1+2*2^9*c.k,101912134538740+c.lower,101912515998903+c.upper)) = pointBounds23154 := by
 decide +kernel
def cuts23155 : List PrefixCut := [⟨38,164498833,164498927⟩,
⟨128,553137469,553137777⟩]
theorem checked23155 : checkPrefixCuts (2^48) 3038904321 9 Manual.Count131072.C023155.packed 128 cuts23155 = true := by
 decide +kernel
def pointBounds23155 : List (Nat × Nat × Nat) := [(3038943232,101912850994750,101913232455316)]
theorem point_links_checked23155 : (cuts23155.take 1).map (fun c => (3038904321-1+2*2^9*c.k,101912686495917+c.lower,101913067956389+c.upper)) = pointBounds23155 := by
 decide +kernel
def cuts23156 : List PrefixCut := [⟨3,12966768,12966775⟩,
⟨96,415763615,415763854⟩,
⟨128,562653094,562653417⟩]
theorem checked23156 : checkPrefixCuts (2^48) 3039035393 9 Manual.Count131072.C023156.packed 128 cuts23156 = true := by
 decide +kernel
def pointBounds23156 : List (Nat × Nat × Nat) := [(3039038464,101913252600154,101913634060941),(3039133696,101913655397001,101914036858020)]
theorem point_links_checked23156 : (cuts23156.take 2).map (fun c => (3039035393-1+2*2^9*c.k,101913239633386+c.lower,101913621094166+c.upper)) = pointBounds23156 := by
 decide +kernel
def cuts23157 : List PrefixCut := [⟨61,261822240,261822389⟩,
⟨128,555312455,555312766⟩]
theorem checked23157 : checkPrefixCuts (2^48) 3039166465 9 Manual.Count131072.C023157.packed 128 cuts23157 = true := by
 decide +kernel
def pointBounds23157 : List (Nat × Nat × Nat) := [(3039228928,101914064108720,101914445569972)]
theorem point_links_checked23157 : (cuts23157.take 1).map (fun c => (3039166465-1+2*2^9*c.k,101913802286480+c.lower,101914183747583+c.upper)) = pointBounds23157 := by
 decide +kernel
def cuts23158 : List PrefixCut := [⟨26,117431279,117431349⟩,
⟨119,516393249,516393546⟩,
⟨128,556029462,556029783⟩]
theorem checked23158 : checkPrefixCuts (2^48) 3039297537 9 Manual.Count131072.C023158.packed 128 cuts23158 = true := by
 decide +kernel
def pointBounds23158 : List (Nat × Nat × Nat) := [(3039324160,101914475030214,101914856491698),(3039419392,101914873992184,101915255453895)]
theorem point_links_checked23158 : (cuts23158.take 2).map (fun c => (3039297537-1+2*2^9*c.k,101914357598935+c.lower,101914739060349+c.upper)) = pointBounds23158 := by
 decide +kernel
def cuts23159 : List PrefixCut := [⟨84,359683719,359683926⟩,
⟨128,549708209,549708526⟩]
theorem checked23159 : checkPrefixCuts (2^48) 3039428609 9 Manual.Count131072.C023159.packed 128 cuts23159 = true := by
 decide +kernel
def pointBounds23159 : List (Nat × Nat × Nat) := [(3039514624,101915273312116,101915654774058)]
theorem point_links_checked23159 : (cuts23159.take 1).map (fun c => (3039428609-1+2*2^9*c.k,101914913628397+c.lower,101915295090132+c.upper)) = pointBounds23159 := by
 decide +kernel
def cuts23160 : List PrefixCut := [⟨49,210579411,210579532⟩,
⟨128,558944720,558945038⟩]
theorem checked23160 : checkPrefixCuts (2^48) 3039559681 9 Manual.Count131072.C023160.packed 128 cuts23160 = true := by
 decide +kernel
def pointBounds23160 : List (Nat × Nat × Nat) := [(3039609856,101915673916017,101916055378190)]
theorem point_links_checked23160 : (cuts23160.take 1).map (fun c => (3039559681-1+2*2^9*c.k,101915463336606+c.lower,101915844798658+c.upper)) = pointBounds23160 := by
 decide +kernel
def cuts23161 : List PrefixCut := [⟨14,63338144,63338182⟩,
⟨107,465861496,465861764⟩,
⟨128,560031812,560032132⟩]
theorem checked23161 : checkPrefixCuts (2^48) 3039690753 9 Manual.Count131072.C023161.packed 128 cuts23161 = true := by
 decide +kernel
def pointBounds23161 : List (Nat × Nat × Nat) := [(3039705088,101916085619470,101916467081878),(3039800320,101916488142822,101916869605460)]
theorem point_links_checked23161 : (cuts23161.take 2).map (fun c => (3039690753-1+2*2^9*c.k,101916022281326+c.lower,101916403743696+c.upper)) = pointBounds23161 := by
 decide +kernel
def cuts23162 : List PrefixCut := [⟨72,311118272,311118450⟩,
⟨128,559822348,559822672⟩]
theorem checked23162 : checkPrefixCuts (2^48) 3039821825 9 Manual.Count131072.C023162.packed 128 cuts23162 = true := by
 decide +kernel
def pointBounds23162 : List (Nat × Nat × Nat) := [(3039895552,101916893431410,101917274894278)]
theorem point_links_checked23162 : (cuts23162.take 1).map (fun c => (3039821825-1+2*2^9*c.k,101916582313138+c.lower,101916963775828+c.upper)) = pointBounds23162 := by
 decide +kernel
def cuts23163 : List PrefixCut := [⟨37,163238433,163238527⟩,
⟨128,561002026,561002351⟩]
theorem checked23163 : checkPrefixCuts (2^48) 3039952897 9 Manual.Count131072.C023163.packed 128 cuts23163 = true := by
 decide +kernel
def pointBounds23163 : List (Nat × Nat × Nat) := [(3039990784,101917305373919,101917686837027)]
theorem point_links_checked23163 : (cuts23163.take 1).map (fun c => (3039952897-1+2*2^9*c.k,101917142135486+c.lower,101917523598500+c.upper)) = pointBounds23163 := by
 decide +kernel
def cuts23164 : List PrefixCut := [⟨2,8425493,8425498⟩,
⟨95,401639794,401640030⟩,
⟨128,544404931,544405249⟩]
theorem checked23164 : checkPrefixCuts (2^48) 3040083969 9 Manual.Count131072.C023164.packed 128 cuts23164 = true := by
 decide +kernel
def pointBounds23164 : List (Nat × Nat × Nat) := [(3040086016,101917711563005,101918093026349),(3040181248,101918104777306,101918486240881)]
theorem point_links_checked23164 : (cuts23164.take 2).map (fun c => (3040083969-1+2*2^9*c.k,101917703137512+c.lower,101918084600851+c.upper)) = pointBounds23164 := by
 decide +kernel
def cuts23165 : List PrefixCut := [⟨60,260713556,260713702⟩,
⟨128,556046793,556047104⟩]
theorem checked23165 : checkPrefixCuts (2^48) 3040215041 9 Manual.Count131072.C023165.packed 128 cuts23165 = true := by
 decide +kernel
def pointBounds23165 : List (Nat × Nat × Nat) := [(3040276480,101918508255999,101918889719802)]
theorem point_links_checked23165 : (cuts23165.take 1).map (fun c => (3040215041-1+2*2^9*c.k,101918247542443+c.lower,101918629006100+c.upper)) = pointBounds23165 := by
 decide +kernel
def cuts23166 : List PrefixCut := [⟨25,108503170,108503233⟩,
⟨118,514733965,514734256⟩,
⟨128,557226375,557226690⟩]
theorem checked23166 : checkPrefixCuts (2^48) 3040346113 9 Manual.Count131072.C023166.packed 128 cuts23166 = true := by
 decide +kernel
def pointBounds23166 : List (Nat × Nat × Nat) := [(3040371712,101918912092406,101919293556437),(3040466944,101919318323201,101919699787460)]
theorem point_links_checked23166 : (cuts23166.take 2).map (fun c => (3040346113-1+2*2^9*c.k,101918803589236+c.lower,101919185053204+c.upper)) = pointBounds23166 := by
 decide +kernel
def cuts23167 : List PrefixCut := [⟨83,357985946,357986155⟩,
⟨128,560627368,560627690⟩]
theorem checked23167 : checkPrefixCuts (2^48) 3040477185 9 Manual.Count131072.C023167.packed 128 cuts23167 = true := by
 decide +kernel
def pointBounds23167 : List (Nat × Nat × Nat) := [(3040562176,101919718801557,101920100266049)]
theorem point_links_checked23167 : (cuts23167.take 1).map (fun c => (3040477185-1+2*2^9*c.k,101919360815611+c.lower,101919742279894+c.upper)) = pointBounds23167 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000098
