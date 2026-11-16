import PlattAssemblyKernel
import PlattCertificates.Count131072.C053008
import PlattCertificates.Count131072.C053009
import PlattCertificates.Count131072.C053010
import PlattCertificates.Count131072.C053011
import PlattCertificates.Count131072.C053012
import PlattCertificates.Count131072.C053013
import PlattCertificates.Count131072.C053014
import PlattCertificates.Count131072.C053015
import PlattCertificates.Count131072.C053016
import PlattCertificates.Count131072.C053017
import PlattCertificates.Count131072.C053018
import PlattCertificates.Count131072.C053019
import PlattCertificates.Count131072.C053020
import PlattCertificates.Count131072.C053021
import PlattCertificates.Count131072.C053022
import PlattCertificates.Count131072.C053023
import PlattCertificates.Count131072.C053024
import PlattCertificates.Count131072.C053025
import PlattCertificates.Count131072.C053026
import PlattCertificates.Count131072.C053027
import PlattCertificates.Count131072.C053028
import PlattCertificates.Count131072.C053029
import PlattCertificates.Count131072.C053030
import PlattCertificates.Count131072.C053031
import PlattCertificates.Count131072.C053032
import PlattCertificates.Count131072.C053033
import PlattCertificates.Count131072.C053034
import PlattCertificates.Count131072.C053035
import PlattCertificates.Count131072.C053036
import PlattCertificates.Count131072.C053037
import PlattCertificates.Count131072.C053038
import PlattCertificates.Count131072.C053039
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000094
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts53008 : List PrefixCut := [⟨64,233784280,233784411⟩]
theorem checked53008 : checkPrefixCuts (2^48) 6951796737 10 Manual.Count131072.C053008.packed 64 cuts53008 = true := by
 decide +kernel
def cuts53009 : List PrefixCut := [⟨21,76644979,76645022⟩,
⟨64,232605705,232605838⟩]
theorem checked53009 : checkPrefixCuts (2^48) 6951927809 10 Manual.Count131072.C053009.packed 64 cuts53009 = true := by
 decide +kernel
def pointBounds53009 : List (Nat × Nat × Nat) := [(6951970816,112383257556587,112383645091557)]
theorem point_links_checked53009 : (cuts53009.take 1).map (fun c => (6951927809-1+2*2^10*c.k,112383180911608+c.lower,112383568446535+c.upper)) = pointBounds53009 := by
 decide +kernel
def cuts53010 : List PrefixCut := [⟨64,233451561,233451695⟩]
theorem checked53010 : checkPrefixCuts (2^48) 6952058881 10 Manual.Count131072.C053010.packed 64 cuts53010 = true := by
 decide +kernel
def pointBounds53010 : List (Nat × Nat × Nat) := [(6952189952,112383646968874,112384034504068)]
theorem point_links_checked53010 : (cuts53010.take 1).map (fun c => (6952058881-1+2*2^10*c.k,112383413517313+c.lower,112383801052373+c.upper)) = pointBounds53010 := by
 decide +kernel
def cuts53011 : List PrefixCut := [⟨64,233123274,233123402⟩]
theorem checked53011 : checkPrefixCuts (2^48) 6952189953 10 Manual.Count131072.C053011.packed 64 cuts53011 = true := by
 decide +kernel
def cuts53012 : List PrefixCut := [⟨43,158665449,158665541⟩,
⟨64,234900256,234900394⟩]
theorem checked53012 : checkPrefixCuts (2^48) 6952321025 10 Manual.Count131072.C053012.packed 64 cuts53012 = true := by
 decide +kernel
def pointBounds53012 : List (Nat × Nat × Nat) := [(6952409088,112384038757597,112384426293011)]
theorem point_links_checked53012 : (cuts53012.take 1).map (fun c => (6952321025-1+2*2^10*c.k,112383880092148+c.lower,112384267627470+c.upper)) = pointBounds53012 := by
 decide +kernel
def cuts53013 : List PrefixCut := [⟨64,235786505,235786640⟩]
theorem checked53013 : checkPrefixCuts (2^48) 6952452097 10 Manual.Count131072.C053013.packed 64 cuts53013 = true := by
 decide +kernel
def cuts53014 : List PrefixCut := [⟨22,80200400,80200447⟩,
⟨64,235903501,235903635⟩]
theorem checked53014 : checkPrefixCuts (2^48) 6952583169 10 Manual.Count131072.C053014.packed 64 cuts53014 = true := by
 decide +kernel
def pointBounds53014 : List (Nat × Nat × Nat) := [(6952628224,112384430979309,112384818514951)]
theorem point_links_checked53014 : (cuts53014.take 1).map (fun c => (6952583169-1+2*2^10*c.k,112384350778909+c.lower,112384738314504+c.upper)) = pointBounds53014 := by
 decide +kernel
def cuts53015 : List PrefixCut := [⟨64,233551004,233551135⟩]
theorem checked53015 : checkPrefixCuts (2^48) 6952714241 10 Manual.Count131072.C053015.packed 64 cuts53015 = true := by
 decide +kernel
def cuts53016 : List PrefixCut := [⟨1,3643506,3643509⟩,
⟨64,231967756,231967894⟩]
theorem checked53016 : checkPrefixCuts (2^48) 6952845313 10 Manual.Count131072.C053016.packed 64 cuts53016 = true := by
 decide +kernel
def pointBounds53016 : List (Nat × Nat × Nat) := [(6952847360,112384823876920,112385211412783)]
theorem point_links_checked53016 : (cuts53016.take 1).map (fun c => (6952845313-1+2*2^10*c.k,112384820233414+c.lower,112385207769274+c.upper)) = pointBounds53016 := by
 decide +kernel
def cuts53017 : List PrefixCut := [⟨44,162577262,162577353⟩,
⟨64,234270891,234271024⟩]
theorem checked53017 : checkPrefixCuts (2^48) 6952976385 10 Manual.Count131072.C053017.packed 64 cuts53017 = true := by
 decide +kernel
def pointBounds53017 : List (Nat × Nat × Nat) := [(6953066496,112385214778432,112385602314521)]
theorem point_links_checked53017 : (cuts53017.take 1).map (fun c => (6952976385-1+2*2^10*c.k,112385052201170+c.lower,112385439737168+c.upper)) = pointBounds53017 := by
 decide +kernel
def cuts53018 : List PrefixCut := [⟨64,232161401,232161534⟩]
theorem checked53018 : checkPrefixCuts (2^48) 6953107457 10 Manual.Count131072.C053018.packed 64 cuts53018 = true := by
 decide +kernel
def cuts53019 : List PrefixCut := [⟨23,84079008,84079055⟩,
⟨64,234140605,234140736⟩]
theorem checked53019 : checkPrefixCuts (2^48) 6953238529 10 Manual.Count131072.C053019.packed 64 cuts53019 = true := by
 decide +kernel
def pointBounds53019 : List (Nat × Nat × Nat) := [(6953285632,112385602712470,112385990248781)]
theorem point_links_checked53019 : (cuts53019.take 1).map (fun c => (6953238529-1+2*2^10*c.k,112385518633462+c.lower,112385906169726+c.upper)) = pointBounds53019 := by
 decide +kernel
def cuts53020 : List PrefixCut := [⟨64,234783881,234784012⟩]
theorem checked53020 : checkPrefixCuts (2^48) 6953369601 10 Manual.Count131072.C053020.packed 64 cuts53020 = true := by
 decide +kernel
def cuts53021 : List PrefixCut := [⟨2,7083927,7083931⟩,
⟨64,234131804,234131934⟩]
theorem checked53021 : checkPrefixCuts (2^48) 6953500673 10 Manual.Count131072.C053021.packed 64 cuts53021 = true := by
 decide +kernel
def pointBounds53021 : List (Nat × Nat × Nat) := [(6953504768,112385994641875,112386382178405)]
theorem point_links_checked53021 : (cuts53021.take 1).map (fun c => (6953500673-1+2*2^10*c.k,112385987557948+c.lower,112386375094474+c.upper)) = pointBounds53021 := by
 decide +kernel
def cuts53022 : List PrefixCut := [⟨45,166447849,166447944⟩,
⟨64,234329760,234329893⟩]
theorem checked53022 : checkPrefixCuts (2^48) 6953631745 10 Manual.Count131072.C053022.packed 64 cuts53022 = true := by
 decide +kernel
def pointBounds53022 : List (Nat × Nat × Nat) := [(6953723904,112386388137601,112386775674352)]
theorem point_links_checked53022 : (cuts53022.take 1).map (fun c => (6953631745-1+2*2^10*c.k,112386221689752+c.lower,112386609226408+c.upper)) = pointBounds53022 := by
 decide +kernel
def cuts53023 : List PrefixCut := [⟨64,234487269,234487403⟩]
theorem checked53023 : checkPrefixCuts (2^48) 6953762817 10 Manual.Count131072.C053023.packed 64 cuts53023 = true := by
 decide +kernel
def cuts53024 : List PrefixCut := [⟨24,87025898,87025946⟩,
⟨64,236142360,236142492⟩]
theorem checked53024 : checkPrefixCuts (2^48) 6953893889 10 Manual.Count131072.C053024.packed 64 cuts53024 = true := by
 decide +kernel
def pointBounds53024 : List (Nat × Nat × Nat) := [(6953943040,112386777532679,112387165069650)]
theorem point_links_checked53024 : (cuts53024.take 1).map (fun c => (6953893889-1+2*2^10*c.k,112386690506781+c.lower,112387078043704+c.upper)) = pointBounds53024 := by
 decide +kernel
def cuts53025 : List PrefixCut := [⟨64,230309385,230309516⟩]
theorem checked53025 : checkPrefixCuts (2^48) 6954024961 10 Manual.Count131072.C053025.packed 64 cuts53025 = true := by
 decide +kernel
def cuts53026 : List PrefixCut := [⟨3,11049884,11049890⟩,
⟨64,235283509,235283646⟩]
theorem checked53026 : checkPrefixCuts (2^48) 6954156033 10 Manual.Count131072.C053026.packed 64 cuts53026 = true := by
 decide +kernel
def pointBounds53026 : List (Nat × Nat × Nat) := [(6954162176,112387168008410,112387555545602)]
theorem point_links_checked53026 : (cuts53026.take 1).map (fun c => (6954156033-1+2*2^10*c.k,112387156958526+c.lower,112387544495712+c.upper)) = pointBounds53026 := by
 decide +kernel
def cuts53027 : List PrefixCut := [⟨46,168860639,168860732⟩,
⟨64,234914799,234914930⟩]
theorem checked53027 : checkPrefixCuts (2^48) 6954287105 10 Manual.Count131072.C053027.packed 64 cuts53027 = true := by
 decide +kernel
def pointBounds53027 : List (Nat × Nat × Nat) := [(6954381312,112387561102674,112387948640090)]
theorem point_links_checked53027 : (cuts53027.take 1).map (fun c => (6954287105-1+2*2^10*c.k,112387392242035+c.lower,112387779779358+c.upper)) = pointBounds53027 := by
 decide +kernel
def cuts53028 : List PrefixCut := [⟨64,233736614,233736745⟩]
theorem checked53028 : checkPrefixCuts (2^48) 6954418177 10 Manual.Count131072.C053028.packed 64 cuts53028 = true := by
 decide +kernel
def cuts53029 : List PrefixCut := [⟨25,90781710,90781759⟩,
⟨64,233732210,233732344⟩]
theorem checked53029 : checkPrefixCuts (2^48) 6954549249 10 Manual.Count131072.C053029.packed 64 cuts53029 = true := by
 decide +kernel
def pointBounds53029 : List (Nat × Nat × Nat) := [(6954600448,112387951675158,112388339212792)]
theorem point_links_checked53029 : (cuts53029.take 1).map (fun c => (6954549249-1+2*2^10*c.k,112387860893448+c.lower,112388248431033+c.upper)) = pointBounds53029 := by
 decide +kernel
def cuts53030 : List PrefixCut := [⟨64,232473167,232473303⟩]
theorem checked53030 : checkPrefixCuts (2^48) 6954680321 10 Manual.Count131072.C053030.packed 64 cuts53030 = true := by
 decide +kernel
def cuts53031 : List PrefixCut := [⟨4,13639045,13639053⟩,
⟨64,231457011,231457144⟩]
theorem checked53031 : checkPrefixCuts (2^48) 6954811393 10 Manual.Count131072.C053031.packed 64 cuts53031 = true := by
 decide +kernel
def pointBounds53031 : List (Nat × Nat × Nat) := [(6954819584,112388340737870,112388728275733)]
theorem point_links_checked53031 : (cuts53031.take 1).map (fun c => (6954811393-1+2*2^10*c.k,112388327098825+c.lower,112388714636680+c.upper)) = pointBounds53031 := by
 decide +kernel
def cuts53032 : List PrefixCut := [⟨47,173336967,173337067⟩,
⟨64,234204661,234204797⟩]
theorem checked53032 : checkPrefixCuts (2^48) 6954942465 10 Manual.Count131072.C053032.packed 64 cuts53032 = true := by
 decide +kernel
def pointBounds53032 : List (Nat × Nat × Nat) := [(6955038720,112388731892803,112389119430891)]
theorem point_links_checked53032 : (cuts53032.take 1).map (fun c => (6954942465-1+2*2^10*c.k,112388558555836+c.lower,112388946093824+c.upper)) = pointBounds53032 := by
 decide +kernel
def cuts53033 : List PrefixCut := [⟨64,234483537,234483671⟩]
theorem checked53033 : checkPrefixCuts (2^48) 6955073537 10 Manual.Count131072.C053033.packed 64 cuts53033 = true := by
 decide +kernel
def cuts53034 : List PrefixCut := [⟨26,92796625,92796677⟩,
⟨64,234236284,234236413⟩]
theorem checked53034 : checkPrefixCuts (2^48) 6955204609 10 Manual.Count131072.C053034.packed 64 cuts53034 = true := by
 decide +kernel
def pointBounds53034 : List (Nat × Nat × Nat) := [(6955257856,112389120040659,112389507578969)]
theorem point_links_checked53034 : (cuts53034.take 1).map (fun c => (6955204609-1+2*2^10*c.k,112389027244034+c.lower,112389414782292+c.upper)) = pointBounds53034 := by
 decide +kernel
def cuts53035 : List PrefixCut := [⟨64,230387354,230387485⟩]
theorem checked53035 : checkPrefixCuts (2^48) 6955335681 10 Manual.Count131072.C053035.packed 64 cuts53035 = true := by
 decide +kernel
def cuts53036 : List PrefixCut := [⟨5,18777210,18777221⟩,
⟨64,235684323,235684454⟩]
theorem checked53036 : checkPrefixCuts (2^48) 6955466753 10 Manual.Count131072.C053036.packed 64 cuts53036 = true := by
 decide +kernel
def pointBounds53036 : List (Nat × Nat × Nat) := [(6955476992,112389510644882,112389898183411)]
theorem point_links_checked53036 : (cuts53036.take 1).map (fun c => (6955466753-1+2*2^10*c.k,112389491867672+c.lower,112389879406190+c.upper)) = pointBounds53036 := by
 decide +kernel
def cuts53037 : List PrefixCut := [⟨48,177003123,177003225⟩,
⟨64,236812942,236813076⟩]
theorem checked53037 : checkPrefixCuts (2^48) 6955597825 10 Manual.Count131072.C053037.packed 64 cuts53037 = true := by
 decide +kernel
def pointBounds53037 : List (Nat × Nat × Nat) := [(6955696128,112389904555118,112390292093869)]
theorem point_links_checked53037 : (cuts53037.take 1).map (fun c => (6955597825-1+2*2^10*c.k,112389727551995+c.lower,112390115090644+c.upper)) = pointBounds53037 := by
 decide +kernel
def cuts53038 : List PrefixCut := [⟨64,232761834,232761965⟩]
theorem checked53038 : checkPrefixCuts (2^48) 6955728897 10 Manual.Count131072.C053038.packed 64 cuts53038 = true := by
 decide +kernel
def cuts53039 : List PrefixCut := [⟨27,98088872,98088927⟩,
⟨64,231907692,231907824⟩]
theorem checked53039 : checkPrefixCuts (2^48) 6955859969 10 Manual.Count131072.C053039.packed 64 cuts53039 = true := by
 decide +kernel
def pointBounds53039 : List (Nat × Nat × Nat) := [(6955915264,112390295215643,112390682754612)]
theorem point_links_checked53039 : (cuts53039.take 1).map (fun c => (6955859969-1+2*2^10*c.k,112390197126771+c.lower,112390584665685+c.upper)) = pointBounds53039 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000094
