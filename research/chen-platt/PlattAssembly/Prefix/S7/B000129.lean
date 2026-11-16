import PlattAssemblyKernel
import PlattCertificates.Count131072.C064128
import PlattCertificates.Count131072.C064129
import PlattCertificates.Count131072.C064130
import PlattCertificates.Count131072.C064131
import PlattCertificates.Count131072.C064132
import PlattCertificates.Count131072.C064133
import PlattCertificates.Count131072.C064134
import PlattCertificates.Count131072.C064135
import PlattCertificates.Count131072.C064136
import PlattCertificates.Count131072.C064137
import PlattCertificates.Count131072.C064138
import PlattCertificates.Count131072.C064139
import PlattCertificates.Count131072.C064140
import PlattCertificates.Count131072.C064141
import PlattCertificates.Count131072.C064142
import PlattCertificates.Count131072.C064143
import PlattCertificates.Count131072.C064144
import PlattCertificates.Count131072.C064145
import PlattCertificates.Count131072.C064146
import PlattCertificates.Count131072.C064147
import PlattCertificates.Count131072.C064148
import PlattCertificates.Count131072.C064149
import PlattCertificates.Count131072.C064150
import PlattCertificates.Count131072.C064151
import PlattCertificates.Count131072.C064152
import PlattCertificates.Count131072.C064153
import PlattCertificates.Count131072.C064154
import PlattCertificates.Count131072.C064155
import PlattCertificates.Count131072.C064156
import PlattCertificates.Count131072.C064157
import PlattCertificates.Count131072.C064158
import PlattCertificates.Count131072.C064159
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000129
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts64128 : List PrefixCut := [⟨64,190151744,190151854⟩]
theorem checked64128 : checkPrefixCuts (2^48) 8409317377 10 Manual.Count131072.C064128.packed 64 cuts64128 = true := by
 decide +kernel
def cuts64129 : List PrefixCut := [⟨63,190215751,190215863⟩,
⟨64,193194648,193194761⟩]
theorem checked64129 : checkPrefixCuts (2^48) 8409448449 10 Manual.Count131072.C064129.packed 64 cuts64129 = true := by
 decide +kernel
def pointBounds64129 : List (Nat × Nat × Nat) := [(8409577472,114737577109014,114737965987254)]
theorem point_links_checked64129 : (cuts64129.take 1).map (fun c => (8409448449-1+2*2^10*c.k,114737386893263+c.lower,114737775771391+c.upper)) = pointBounds64129 := by
 decide +kernel
def cuts64130 : List PrefixCut := [⟨64,191484641,191484753⟩]
theorem checked64130 : checkPrefixCuts (2^48) 8409579521 10 Manual.Count131072.C064130.packed 64 cuts64130 = true := by
 decide +kernel
def cuts64131 : List PrefixCut := [⟨64,189942037,189942148⟩]
theorem checked64131 : checkPrefixCuts (2^48) 8409710593 10 Manual.Count131072.C064131.packed 64 cuts64131 = true := by
 decide +kernel
def pointBounds64131 : List (Nat × Nat × Nat) := [(8409841664,114737961514589,114738350393053)]
theorem point_links_checked64131 : (cuts64131.take 1).map (fun c => (8409710593-1+2*2^10*c.k,114737771572552+c.lower,114738160450905+c.upper)) = pointBounds64131 := by
 decide +kernel
def cuts64132 : List PrefixCut := [⟨64,190742349,190742464⟩]
theorem checked64132 : checkPrefixCuts (2^48) 8409841665 10 Manual.Count131072.C064132.packed 64 cuts64132 = true := by
 decide +kernel
def cuts64133 : List PrefixCut := [⟨64,190304264,190304373⟩]
theorem checked64133 : checkPrefixCuts (2^48) 8409972737 10 Manual.Count131072.C064133.packed 64 cuts64133 = true := by
 decide +kernel
def cuts64134 : List PrefixCut := [⟨1,3146054,3146055⟩,
⟨64,193045711,193045826⟩]
theorem checked64134 : checkPrefixCuts (2^48) 8410103809 10 Manual.Count131072.C064134.packed 64 cuts64134 = true := by
 decide +kernel
def pointBounds64134 : List (Nat × Nat × Nat) := [(8410105856,114738345707256,114738734585945)]
theorem point_links_checked64134 : (cuts64134.take 1).map (fun c => (8410103809-1+2*2^10*c.k,114738342561202+c.lower,114738731439890+c.upper)) = pointBounds64134 := by
 decide +kernel
def cuts64135 : List PrefixCut := [⟨64,193511268,193511378⟩]
theorem checked64135 : checkPrefixCuts (2^48) 8410234881 10 Manual.Count131072.C064135.packed 64 cuts64135 = true := by
 decide +kernel
def cuts64136 : List PrefixCut := [⟨2,6024170,6024173⟩,
⟨64,194110665,194110766⟩]
theorem checked64136 : checkPrefixCuts (2^48) 8410365953 10 Manual.Count131072.C064136.packed 64 cuts64136 = true := by
 decide +kernel
def pointBounds64136 : List (Nat × Nat × Nat) := [(8410370048,114738735142351,114739124021267)]
theorem point_links_checked64136 : (cuts64136.take 1).map (fun c => (8410365953-1+2*2^10*c.k,114738729118181+c.lower,114739117997094+c.upper)) = pointBounds64136 := by
 decide +kernel
def cuts64137 : List PrefixCut := [⟨64,189455765,189455874⟩]
theorem checked64137 : checkPrefixCuts (2^48) 8410497025 10 Manual.Count131072.C064137.packed 64 cuts64137 = true := by
 decide +kernel
def cuts64138 : List PrefixCut := [⟨3,8734771,8734777⟩,
⟨64,192297433,192297547⟩]
theorem checked64138 : checkPrefixCuts (2^48) 8410628097 10 Manual.Count131072.C064138.packed 64 cuts64138 = true := by
 decide +kernel
def pointBounds64138 : List (Nat × Nat × Nat) := [(8410634240,114739121419382,114739510298511)]
theorem point_links_checked64138 : (cuts64138.take 1).map (fun c => (8410628097-1+2*2^10*c.k,114739112684611+c.lower,114739501563734+c.upper)) = pointBounds64138 := by
 decide +kernel
def cuts64139 : List PrefixCut := [⟨64,190420338,190420447⟩]
theorem checked64139 : checkPrefixCuts (2^48) 8410759169 10 Manual.Count131072.C064139.packed 64 cuts64139 = true := by
 decide +kernel
def cuts64140 : List PrefixCut := [⟨4,11378275,11378281⟩,
⟨64,192793416,192793525⟩]
theorem checked64140 : checkPrefixCuts (2^48) 8410890241 10 Manual.Count131072.C064140.packed 64 cuts64140 = true := by
 decide +kernel
def pointBounds64140 : List (Nat × Nat × Nat) := [(8410898432,114739506780657,114739895660009)]
theorem point_links_checked64140 : (cuts64140.take 1).map (fun c => (8410890241-1+2*2^10*c.k,114739495402382+c.lower,114739884281728+c.upper)) = pointBounds64140 := by
 decide +kernel
def cuts64141 : List PrefixCut := [⟨64,191786459,191786578⟩]
theorem checked64141 : checkPrefixCuts (2^48) 8411021313 10 Manual.Count131072.C064141.packed 64 cuts64141 = true := by
 decide +kernel
def cuts64142 : List PrefixCut := [⟨5,15293260,15293269⟩,
⟨64,188805170,188805281⟩]
theorem checked64142 : checkPrefixCuts (2^48) 8411152385 10 Manual.Count131072.C064142.packed 64 cuts64142 = true := by
 decide +kernel
def pointBounds64142 : List (Nat × Nat × Nat) := [(8411162624,114739895275517,114740284155100)]
theorem point_links_checked64142 : (cuts64142.take 1).map (fun c => (8411152385-1+2*2^10*c.k,114739879982257+c.lower,114740268861831+c.upper)) = pointBounds64142 := by
 decide +kernel
def cuts64143 : List PrefixCut := [⟨64,193687926,193688039⟩]
theorem checked64143 : checkPrefixCuts (2^48) 8411283457 10 Manual.Count131072.C064143.packed 64 cuts64143 = true := by
 decide +kernel
def cuts64144 : List PrefixCut := [⟨6,18304490,18304501⟩,
⟨64,191275556,191275670⟩]
theorem checked64144 : checkPrefixCuts (2^48) 8411414529 10 Manual.Count131072.C064144.packed 64 cuts64144 = true := by
 decide +kernel
def pointBounds64144 : List (Nat × Nat × Nat) := [(8411426816,114740280779843,114740669659652)]
theorem point_links_checked64144 : (cuts64144.take 1).map (fun c => (8411414529-1+2*2^10*c.k,114740262475353+c.lower,114740651355151+c.upper)) = pointBounds64144 := by
 decide +kernel
def cuts64145 : List PrefixCut := [⟨64,193614962,193615076⟩]
theorem checked64145 : checkPrefixCuts (2^48) 8411545601 10 Manual.Count131072.C064145.packed 64 cuts64145 = true := by
 decide +kernel
def cuts64146 : List PrefixCut := [⟨7,20980909,20980919⟩,
⟨64,190165355,190165460⟩]
theorem checked64146 : checkPrefixCuts (2^48) 8411676673 10 Manual.Count131072.C064146.packed 64 cuts64146 = true := by
 decide +kernel
def pointBounds64146 : List (Nat × Nat × Nat) := [(8411691008,114740668346780,114741057226816)]
theorem point_links_checked64146 : (cuts64146.take 1).map (fun c => (8411676673-1+2*2^10*c.k,114740647365871+c.lower,114741036245897+c.upper)) = pointBounds64146 := by
 decide +kernel
def cuts64147 : List PrefixCut := [⟨64,191668167,191668280⟩]
theorem checked64147 : checkPrefixCuts (2^48) 8411807745 10 Manual.Count131072.C064147.packed 64 cuts64147 = true := by
 decide +kernel
def cuts64148 : List PrefixCut := [⟨8,24493690,24493704⟩,
⟨64,188854451,188854561⟩]
theorem checked64148 : checkPrefixCuts (2^48) 8411938817 10 Manual.Count131072.C064148.packed 64 cuts64148 = true := by
 decide +kernel
def pointBounds64148 : List (Nat × Nat × Nat) := [(8411955200,114741053693083,114741442573341)]
theorem point_links_checked64148 : (cuts64148.take 1).map (fun c => (8411938817-1+2*2^10*c.k,114741029199393+c.lower,114741418079637+c.upper)) = pointBounds64148 := by
 decide +kernel
def cuts64149 : List PrefixCut := [⟨64,193535975,193536083⟩]
theorem checked64149 : checkPrefixCuts (2^48) 8412069889 10 Manual.Count131072.C064149.packed 64 cuts64149 = true := by
 decide +kernel
def cuts64150 : List PrefixCut := [⟨9,26500541,26500556⟩,
⟨64,192161095,192161203⟩]
theorem checked64150 : checkPrefixCuts (2^48) 8412200961 10 Manual.Count131072.C064150.packed 64 cuts64150 = true := by
 decide +kernel
def pointBounds64150 : List (Nat × Nat × Nat) := [(8412219392,114741438090360,114741826970837)]
theorem point_links_checked64150 : (cuts64150.take 1).map (fun c => (8412200961-1+2*2^10*c.k,114741411589819+c.lower,114741800470281+c.upper)) = pointBounds64150 := by
 decide +kernel
def cuts64151 : List PrefixCut := [⟨64,191488904,191489005⟩]
theorem checked64151 : checkPrefixCuts (2^48) 8412332033 10 Manual.Count131072.C064151.packed 64 cuts64151 = true := by
 decide +kernel
def cuts64152 : List PrefixCut := [⟨10,30347522,30347539⟩,
⟨64,192288936,192289046⟩]
theorem checked64152 : checkPrefixCuts (2^48) 8412463105 10 Manual.Count131072.C064152.packed 64 cuts64152 = true := by
 decide +kernel
def pointBounds64152 : List (Nat × Nat × Nat) := [(8412483584,114741825587340,114742214468028)]
theorem point_links_checked64152 : (cuts64152.take 1).map (fun c => (8412463105-1+2*2^10*c.k,114741795239818+c.lower,114742184120489+c.upper)) = pointBounds64152 := by
 decide +kernel
def cuts64153 : List PrefixCut := [⟨64,190646485,190646601⟩]
theorem checked64153 : checkPrefixCuts (2^48) 8412594177 10 Manual.Count131072.C064153.packed 64 cuts64153 = true := by
 decide +kernel
def cuts64154 : List PrefixCut := [⟨11,34127349,34127367⟩,
⟨64,195327636,195327741⟩]
theorem checked64154 : checkPrefixCuts (2^48) 8412725249 10 Manual.Count131072.C064154.packed 64 cuts64154 = true := by
 decide +kernel
def pointBounds64154 : List (Nat × Nat × Nat) := [(8412747776,114742212302588,114742601183503)]
theorem point_links_checked64154 : (cuts64154.take 1).map (fun c => (8412725249-1+2*2^10*c.k,114742178175239+c.lower,114742567056136+c.upper)) = pointBounds64154 := by
 decide +kernel
def cuts64155 : List PrefixCut := [⟨64,193384047,193384157⟩]
theorem checked64155 : checkPrefixCuts (2^48) 8412856321 10 Manual.Count131072.C064155.packed 64 cuts64155 = true := by
 decide +kernel
def cuts64156 : List PrefixCut := [⟨12,34293566,34293586⟩,
⟨64,187659891,187660002⟩]
theorem checked64156 : checkPrefixCuts (2^48) 8412987393 10 Manual.Count131072.C064156.packed 64 cuts64156 = true := by
 decide +kernel
def pointBounds64156 : List (Nat × Nat × Nat) := [(8413011968,114742601180488,114742990061620)]
theorem point_links_checked64156 : (cuts64156.take 1).map (fun c => (8412987393-1+2*2^10*c.k,114742566886922+c.lower,114742955768034+c.upper)) = pointBounds64156 := by
 decide +kernel
def cuts64157 : List PrefixCut := [⟨64,192876185,192876298⟩]
theorem checked64157 : checkPrefixCuts (2^48) 8413118465 10 Manual.Count131072.C064157.packed 64 cuts64157 = true := by
 decide +kernel
def cuts64158 : List PrefixCut := [⟨13,36801700,36801723⟩,
⟨64,189427206,189427311⟩]
theorem checked64158 : checkPrefixCuts (2^48) 8413249537 10 Manual.Count131072.C064158.packed 64 cuts64158 = true := by
 decide +kernel
def pointBounds64158 : List (Nat × Nat × Nat) := [(8413276160,114742984224698,114743373106057)]
theorem point_links_checked64158 : (cuts64158.take 1).map (fun c => (8413249537-1+2*2^10*c.k,114742947422998+c.lower,114743336304334+c.upper)) = pointBounds64158 := by
 decide +kernel
def cuts64159 : List PrefixCut := [⟨64,193070898,193071013⟩]
theorem checked64159 : checkPrefixCuts (2^48) 8413380609 10 Manual.Count131072.C064159.packed 64 cuts64159 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000129
