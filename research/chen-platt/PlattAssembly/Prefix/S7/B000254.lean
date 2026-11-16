import PlattAssemblyKernel
import PlattCertificates.Count131072.C068128
import PlattCertificates.Count131072.C068129
import PlattCertificates.Count131072.C068130
import PlattCertificates.Count131072.C068131
import PlattCertificates.Count131072.C068132
import PlattCertificates.Count131072.C068133
import PlattCertificates.Count131072.C068134
import PlattCertificates.Count131072.C068135
import PlattCertificates.Count131072.C068136
import PlattCertificates.Count131072.C068137
import PlattCertificates.Count131072.C068138
import PlattCertificates.Count131072.C068139
import PlattCertificates.Count131072.C068140
import PlattCertificates.Count131072.C068141
import PlattCertificates.Count131072.C068142
import PlattCertificates.Count131072.C068143
import PlattCertificates.Count131072.C068144
import PlattCertificates.Count131072.C068145
import PlattCertificates.Count131072.C068146
import PlattCertificates.Count131072.C068147
import PlattCertificates.Count131072.C068148
import PlattCertificates.Count131072.C068149
import PlattCertificates.Count131072.C068150
import PlattCertificates.Count131072.C068151
import PlattCertificates.Count131072.C068152
import PlattCertificates.Count131072.C068153
import PlattCertificates.Count131072.C068154
import PlattCertificates.Count131072.C068155
import PlattCertificates.Count131072.C068156
import PlattCertificates.Count131072.C068157
import PlattCertificates.Count131072.C068158
import PlattCertificates.Count131072.C068159
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000254
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts68128 : List PrefixCut := [⟨64,180189636,180189743⟩]
theorem checked68128 : checkPrefixCuts (2^48) 8933605377 10 Manual.Count131072.C068128.packed 64 cuts68128 = true := by
 decide +kernel
def cuts68129 : List PrefixCut := [⟨55,154005058,154005151⟩,
⟨64,179462337,179462445⟩]
theorem checked68129 : checkPrefixCuts (2^48) 8933736449 10 Manual.Count131072.C068129.packed 64 cuts68129 = true := by
 decide +kernel
def pointBounds68129 : List (Nat × Nat × Nat) := [(8933849088,115481435726895,115481825037205)]
theorem point_links_checked68129 : (cuts68129.take 1).map (fun c => (8933736449-1+2*2^10*c.k,115481281721837+c.lower,115481671032054+c.upper)) = pointBounds68129 := by
 decide +kernel
def cuts68130 : List PrefixCut := [⟨64,182043227,182043333⟩]
theorem checked68130 : checkPrefixCuts (2^48) 8933867521 10 Manual.Count131072.C068130.packed 64 cuts68130 = true := by
 decide +kernel
def cuts68131 : List PrefixCut := [⟨64,180087196,180087295⟩]
theorem checked68131 : checkPrefixCuts (2^48) 8933998593 10 Manual.Count131072.C068131.packed 64 cuts68131 = true := by
 decide +kernel
def pointBounds68131 : List (Nat × Nat × Nat) := [(8934129664,115481823314597,115482212625127)]
theorem point_links_checked68131 : (cuts68131.take 1).map (fun c => (8933998593-1+2*2^10*c.k,115481643227401+c.lower,115482032537832+c.upper)) = pointBounds68131 := by
 decide +kernel
def cuts68132 : List PrefixCut := [⟨64,180116048,180116154⟩]
theorem checked68132 : checkPrefixCuts (2^48) 8934129665 10 Manual.Count131072.C068132.packed 64 cuts68132 = true := by
 decide +kernel
def cuts68133 : List PrefixCut := [⟨64,179199761,179199867⟩]
theorem checked68133 : checkPrefixCuts (2^48) 8934260737 10 Manual.Count131072.C068133.packed 64 cuts68133 = true := by
 decide +kernel
def cuts68134 : List PrefixCut := [⟨9,25676264,25676280⟩,
⟨64,178850597,178850709⟩]
theorem checked68134 : checkPrefixCuts (2^48) 8934391809 10 Manual.Count131072.C068134.packed 64 cuts68134 = true := by
 decide +kernel
def pointBounds68134 : List (Nat × Nat × Nat) := [(8934410240,115482208306670,115482597617428)]
theorem point_links_checked68134 : (cuts68134.take 1).map (fun c => (8934391809-1+2*2^10*c.k,115482182630406+c.lower,115482571941148+c.upper)) = pointBounds68134 := by
 decide +kernel
def cuts68135 : List PrefixCut := [⟨64,179320528,179320629⟩]
theorem checked68135 : checkPrefixCuts (2^48) 8934522881 10 Manual.Count131072.C068135.packed 64 cuts68135 = true := by
 decide +kernel
def cuts68136 : List PrefixCut := [⟨18,49933305,49933333⟩,
⟨64,179664433,179664538⟩]
theorem checked68136 : checkPrefixCuts (2^48) 8934653953 10 Manual.Count131072.C068136.packed 64 cuts68136 = true := by
 decide +kernel
def pointBounds68136 : List (Nat × Nat × Nat) := [(8934690816,115482590734836,115482980045819)]
theorem point_links_checked68136 : (cuts68136.take 1).map (fun c => (8934653953-1+2*2^10*c.k,115482540801531+c.lower,115482930112486+c.upper)) = pointBounds68136 := by
 decide +kernel
def cuts68137 : List PrefixCut := [⟨64,180669899,180670001⟩]
theorem checked68137 : checkPrefixCuts (2^48) 8934785025 10 Manual.Count131072.C068137.packed 64 cuts68137 = true := by
 decide +kernel
def cuts68138 : List PrefixCut := [⟨27,74944934,74944979⟩,
⟨64,179627652,179627758⟩]
theorem checked68138 : checkPrefixCuts (2^48) 8934916097 10 Manual.Count131072.C068138.packed 64 cuts68138 = true := by
 decide +kernel
def pointBounds68138 : List (Nat × Nat × Nat) := [(8934971392,115482976080797,115483365392004)]
theorem point_links_checked68138 : (cuts68138.take 1).map (fun c => (8934916097-1+2*2^10*c.k,115482901135863+c.lower,115483290447025+c.upper)) = pointBounds68138 := by
 decide +kernel
def cuts68139 : List PrefixCut := [⟨64,178994983,178995092⟩]
theorem checked68139 : checkPrefixCuts (2^48) 8935047169 10 Manual.Count131072.C068139.packed 64 cuts68139 = true := by
 decide +kernel
def cuts68140 : List PrefixCut := [⟨36,100364565,100364627⟩,
⟨64,179527874,179527985⟩]
theorem checked68140 : checkPrefixCuts (2^48) 8935178241 10 Manual.Count131072.C068140.packed 64 cuts68140 = true := by
 decide +kernel
def pointBounds68140 : List (Nat × Nat × Nat) := [(8935251968,115483360123063,115483749434502)]
theorem point_links_checked68140 : (cuts68140.take 1).map (fun c => (8935178241-1+2*2^10*c.k,115483259758498+c.lower,115483649069875+c.upper)) = pointBounds68140 := by
 decide +kernel
def cuts68141 : List PrefixCut := [⟨64,178265208,178265311⟩]
theorem checked68141 : checkPrefixCuts (2^48) 8935309313 10 Manual.Count131072.C068141.packed 64 cuts68141 = true := by
 decide +kernel
def cuts68142 : List PrefixCut := [⟨45,125467655,125467726⟩,
⟨64,178609099,178609200⟩]
theorem checked68142 : checkPrefixCuts (2^48) 8935440385 10 Manual.Count131072.C068142.packed 64 cuts68142 = true := by
 decide +kernel
def pointBounds68142 : List (Nat × Nat × Nat) := [(8935532544,115483743019235,115484132330897)]
theorem point_links_checked68142 : (cuts68142.take 1).map (fun c => (8935440385-1+2*2^10*c.k,115483617551580+c.lower,115484006863171+c.upper)) = pointBounds68142 := by
 decide +kernel
def cuts68143 : List PrefixCut := [⟨64,179803495,179803598⟩]
theorem checked68143 : checkPrefixCuts (2^48) 8935571457 10 Manual.Count131072.C068143.packed 64 cuts68143 = true := by
 decide +kernel
def cuts68144 : List PrefixCut := [⟨54,153026188,153026278⟩,
⟨64,180525342,180525451⟩]
theorem checked68144 : checkPrefixCuts (2^48) 8935702529 10 Manual.Count131072.C068144.packed 64 cuts68144 = true := by
 decide +kernel
def pointBounds68144 : List (Nat × Nat × Nat) := [(8935813120,115484128990362,115484518302247)]
theorem point_links_checked68144 : (cuts68144.take 1).map (fun c => (8935702529-1+2*2^10*c.k,115483975964174+c.lower,115484365275969+c.upper)) = pointBounds68144 := by
 decide +kernel
def cuts68145 : List PrefixCut := [⟨64,181593697,181593803⟩]
theorem checked68145 : checkPrefixCuts (2^48) 8935833601 10 Manual.Count131072.C068145.packed 64 cuts68145 = true := by
 decide +kernel
def cuts68146 : List PrefixCut := [⟨63,174440780,174440881⟩,
⟨64,177370154,177370257⟩]
theorem checked68146 : checkPrefixCuts (2^48) 8935964673 10 Manual.Count131072.C068146.packed 64 cuts68146 = true := by
 decide +kernel
def pointBounds68146 : List (Nat × Nat × Nat) := [(8936093696,115484512523993,115484901836104)]
theorem point_links_checked68146 : (cuts68146.take 1).map (fun c => (8935964673-1+2*2^10*c.k,115484338083213+c.lower,115484727395223+c.upper)) = pointBounds68146 := by
 decide +kernel
def cuts68147 : List PrefixCut := [⟨64,181966332,181966438⟩]
theorem checked68147 : checkPrefixCuts (2^48) 8936095745 10 Manual.Count131072.C068147.packed 64 cuts68147 = true := by
 decide +kernel
def cuts68148 : List PrefixCut := [⟨64,180861241,180861345⟩]
theorem checked68148 : checkPrefixCuts (2^48) 8936226817 10 Manual.Count131072.C068148.packed 64 cuts68148 = true := by
 decide +kernel
def cuts68149 : List PrefixCut := [⟨8,22804328,22804342⟩,
⟨64,182968898,182969009⟩]
theorem checked68149 : checkPrefixCuts (2^48) 8936357889 10 Manual.Count131072.C068149.packed 64 cuts68149 = true := by
 decide +kernel
def pointBounds68149 : List (Nat × Nat × Nat) := [(8936374272,115484901085268,115485290397605)]
theorem point_links_checked68149 : (cuts68149.take 1).map (fun c => (8936357889-1+2*2^10*c.k,115484878280940+c.lower,115485267593263+c.upper)) = pointBounds68149 := by
 decide +kernel
def cuts68150 : List PrefixCut := [⟨64,180351975,180352078⟩]
theorem checked68150 : checkPrefixCuts (2^48) 8936488961 10 Manual.Count131072.C068150.packed 64 cuts68150 = true := by
 decide +kernel
def cuts68151 : List PrefixCut := [⟨17,47812046,47812070⟩,
⟨64,177987091,177987184⟩]
theorem checked68151 : checkPrefixCuts (2^48) 8936620033 10 Manual.Count131072.C068151.packed 64 cuts68151 = true := by
 decide +kernel
def pointBounds68151 : List (Nat × Nat × Nat) := [(8936654848,115485289413859,115485678726420)]
theorem point_links_checked68151 : (cuts68151.take 1).map (fun c => (8936620033-1+2*2^10*c.k,115485241601813+c.lower,115485630914350+c.upper)) = pointBounds68151 := by
 decide +kernel
def cuts68152 : List PrefixCut := [⟨64,179464782,179464892⟩]
theorem checked68152 : checkPrefixCuts (2^48) 8936751105 10 Manual.Count131072.C068152.packed 64 cuts68152 = true := by
 decide +kernel
def cuts68153 : List PrefixCut := [⟨26,72534775,72534820⟩,
⟨64,178674766,178674871⟩]
theorem checked68153 : checkPrefixCuts (2^48) 8936882177 10 Manual.Count131072.C068153.packed 64 cuts68153 = true := by
 decide +kernel
def pointBounds68153 : List (Nat × Nat × Nat) := [(8936935424,115485671588461,115486060901246)]
theorem point_links_checked68153 : (cuts68153.take 1).map (fun c => (8936882177-1+2*2^10*c.k,115485599053686+c.lower,115485988366426+c.upper)) = pointBounds68153 := by
 decide +kernel
def cuts68154 : List PrefixCut := [⟨64,179963443,179963547⟩]
theorem checked68154 : checkPrefixCuts (2^48) 8937013249 10 Manual.Count131072.C068154.packed 64 cuts68154 = true := by
 decide +kernel
def cuts68155 : List PrefixCut := [⟨35,99460651,99460701⟩,
⟨64,180181283,180181384⟩]
theorem checked68155 : checkPrefixCuts (2^48) 8937144321 10 Manual.Count131072.C068155.packed 64 cuts68155 = true := by
 decide +kernel
def pointBounds68155 : List (Nat × Nat × Nat) := [(8937216000,115486057152546,115486446465545)]
theorem point_links_checked68155 : (cuts68155.take 1).map (fun c => (8937144321-1+2*2^10*c.k,115485957691895+c.lower,115486347004844+c.upper)) = pointBounds68155 := by
 decide +kernel
def cuts68156 : List PrefixCut := [⟨64,180273103,180273210⟩]
theorem checked68156 : checkPrefixCuts (2^48) 8937275393 10 Manual.Count131072.C068156.packed 64 cuts68156 = true := by
 decide +kernel
def cuts68157 : List PrefixCut := [⟨44,124117323,124117393⟩,
⟨64,180301966,180302069⟩]
theorem checked68157 : checkPrefixCuts (2^48) 8937406465 10 Manual.Count131072.C068157.packed 64 cuts68157 = true := by
 decide +kernel
def pointBounds68157 : List (Nat × Nat × Nat) := [(8937496576,115486442263604,115486831576831)]
theorem point_links_checked68157 : (cuts68157.take 1).map (fun c => (8937406465-1+2*2^10*c.k,115486318146281+c.lower,115486707459438+c.upper)) = pointBounds68157 := by
 decide +kernel
def cuts68158 : List PrefixCut := [⟨64,181842505,181842608⟩]
theorem checked68158 : checkPrefixCuts (2^48) 8937537537 10 Manual.Count131072.C068158.packed 64 cuts68158 = true := by
 decide +kernel
def cuts68159 : List PrefixCut := [⟨53,150063708,150063799⟩,
⟨64,181745342,181745453⟩]
theorem checked68159 : checkPrefixCuts (2^48) 8937668609 10 Manual.Count131072.C068159.packed 64 cuts68159 = true := by
 decide +kernel
def pointBounds68159 : List (Nat × Nat × Nat) := [(8937777152,115486830354460,115487219667914)]
theorem point_links_checked68159 : (cuts68159.take 1).map (fun c => (8937668609-1+2*2^10*c.k,115486680290752+c.lower,115487069604115+c.upper)) = pointBounds68159 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000254
