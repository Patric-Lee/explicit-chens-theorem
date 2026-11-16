import PlattAssemblyKernel
import PlattCertificates.Count131072.C074000
import PlattCertificates.Count131072.C074001
import PlattCertificates.Count131072.C074002
import PlattCertificates.Count131072.C074003
import PlattCertificates.Count131072.C074004
import PlattCertificates.Count131072.C074005
import PlattCertificates.Count131072.C074006
import PlattCertificates.Count131072.C074007
import PlattCertificates.Count131072.C074008
import PlattCertificates.Count131072.C074009
import PlattCertificates.Count131072.C074010
import PlattCertificates.Count131072.C074011
import PlattCertificates.Count131072.C074012
import PlattCertificates.Count131072.C074013
import PlattCertificates.Count131072.C074014
import PlattCertificates.Count131072.C074015
import PlattCertificates.Count131072.C074016
import PlattCertificates.Count131072.C074017
import PlattCertificates.Count131072.C074018
import PlattCertificates.Count131072.C074019
import PlattCertificates.Count131072.C074020
import PlattCertificates.Count131072.C074021
import PlattCertificates.Count131072.C074022
import PlattCertificates.Count131072.C074023
import PlattCertificates.Count131072.C074024
import PlattCertificates.Count131072.C074025
import PlattCertificates.Count131072.C074026
import PlattCertificates.Count131072.C074027
import PlattCertificates.Count131072.C074028
import PlattCertificates.Count131072.C074029
import PlattCertificates.Count131072.C074030
import PlattCertificates.Count131072.C074031
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000125
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts74000 : List PrefixCut := [⟨63,160733802,160733903⟩,
⟨64,163344512,163344615⟩]
theorem checked74000 : checkPrefixCuts (2^48) 9703260161 10 Manual.Count131072.C074000.packed 64 cuts74000 = true := by
 decide +kernel
def pointBounds74000 : List (Nat × Nat × Nat) := [(9703389184,116494694793406,116495084702636)]
theorem point_links_checked74000 : (cuts74000.take 1).map (fun c => (9703260161-1+2*2^10*c.k,116494534059604+c.lower,116494923968733+c.upper)) = pointBounds74000 := by
 decide +kernel
def cuts74001 : List PrefixCut := [⟨64,166504156,166504256⟩]
theorem checked74001 : checkPrefixCuts (2^48) 9703391233 10 Manual.Count131072.C074001.packed 64 cuts74001 = true := by
 decide +kernel
def cuts74002 : List PrefixCut := [⟨64,164210325,164210419⟩]
theorem checked74002 : checkPrefixCuts (2^48) 9703522305 10 Manual.Count131072.C074002.packed 64 cuts74002 = true := by
 decide +kernel
def cuts74003 : List PrefixCut := [⟨20,52125659,52125691⟩,
⟨64,165832503,165832601⟩]
theorem checked74003 : checkPrefixCuts (2^48) 9703653377 10 Manual.Count131072.C074003.packed 64 cuts74003 = true := by
 decide +kernel
def pointBounds74003 : List (Nat × Nat × Nat) := [(9703694336,116495080244256,116495470153714)]
theorem point_links_checked74003 : (cuts74003.take 1).map (fun c => (9703653377-1+2*2^10*c.k,116495028118597+c.lower,116495418028023+c.upper)) = pointBounds74003 := by
 decide +kernel
def cuts74004 : List PrefixCut := [⟨64,164873039,164873138⟩]
theorem checked74004 : checkPrefixCuts (2^48) 9703784449 10 Manual.Count131072.C074004.packed 64 cuts74004 = true := by
 decide +kernel
def cuts74005 : List PrefixCut := [⟨41,105640568,105640631⟩,
⟨64,166031059,166031159⟩]
theorem checked74005 : checkPrefixCuts (2^48) 9703915521 10 Manual.Count131072.C074005.packed 64 cuts74005 = true := by
 decide +kernel
def pointBounds74005 : List (Nat × Nat × Nat) := [(9703999488,116495464464707,116495854374393)]
theorem point_links_checked74005 : (cuts74005.take 1).map (fun c => (9703915521-1+2*2^10*c.k,116495358824139+c.lower,116495748733762+c.upper)) = pointBounds74005 := by
 decide +kernel
def cuts74006 : List PrefixCut := [⟨64,165709748,165709847⟩]
theorem checked74006 : checkPrefixCuts (2^48) 9704046593 10 Manual.Count131072.C074006.packed 64 cuts74006 = true := by
 decide +kernel
def cuts74007 : List PrefixCut := [⟨62,159384393,159384485⟩,
⟨64,164576315,164576410⟩]
theorem checked74007 : checkPrefixCuts (2^48) 9704177665 10 Manual.Count131072.C074007.packed 64 cuts74007 = true := by
 decide +kernel
def pointBounds74007 : List (Nat × Nat × Nat) := [(9704304640,116495849949339,116496239859253)]
theorem point_links_checked74007 : (cuts74007.take 1).map (fun c => (9704177665-1+2*2^10*c.k,116495690564946+c.lower,116496080474768+c.upper)) = pointBounds74007 := by
 decide +kernel
def cuts74008 : List PrefixCut := [⟨64,167967670,167967761⟩]
theorem checked74008 : checkPrefixCuts (2^48) 9704308737 10 Manual.Count131072.C074008.packed 64 cuts74008 = true := by
 decide +kernel
def cuts74009 : List PrefixCut := [⟨64,162309507,162309603⟩]
theorem checked74009 : checkPrefixCuts (2^48) 9704439809 10 Manual.Count131072.C074009.packed 64 cuts74009 = true := by
 decide +kernel
def cuts74010 : List PrefixCut := [⟨19,50902553,50902585⟩,
⟨64,168659237,168659334⟩]
theorem checked74010 : checkPrefixCuts (2^48) 9704570881 10 Manual.Count131072.C074010.packed 64 cuts74010 = true := by
 decide +kernel
def pointBounds74010 : List (Nat × Nat × Nat) := [(9704609792,116496236320991,116496626231127)]
theorem point_links_checked74010 : (cuts74010.take 1).map (fun c => (9704570881-1+2*2^10*c.k,116496185418438+c.lower,116496575328542+c.upper)) = pointBounds74010 := by
 decide +kernel
def cuts74011 : List PrefixCut := [⟨64,165205501,165205604⟩]
theorem checked74011 : checkPrefixCuts (2^48) 9704701953 10 Manual.Count131072.C074011.packed 64 cuts74011 = true := by
 decide +kernel
def cuts74012 : List PrefixCut := [⟨40,104963512,104963571⟩,
⟨64,166711455,166711548⟩]
theorem checked74012 : checkPrefixCuts (2^48) 9704833025 10 Manual.Count131072.C074012.packed 64 cuts74012 = true := by
 decide +kernel
def pointBounds74012 : List (Nat × Nat × Nat) := [(9704914944,116496624246688,116497014157051)]
theorem point_links_checked74012 : (cuts74012.take 1).map (fun c => (9704833025-1+2*2^10*c.k,116496519283176+c.lower,116496909193480+c.upper)) = pointBounds74012 := by
 decide +kernel
def cuts74013 : List PrefixCut := [⟨64,165520073,165520169⟩]
theorem checked74013 : checkPrefixCuts (2^48) 9704964097 10 Manual.Count131072.C074013.packed 64 cuts74013 = true := by
 decide +kernel
def cuts74014 : List PrefixCut := [⟨61,155540990,155541092⟩,
⟨64,163226629,163226736⟩]
theorem checked74014 : checkPrefixCuts (2^48) 9705095169 10 Manual.Count131072.C074014.packed 64 cuts74014 = true := by
 decide +kernel
def pointBounds74014 : List (Nat × Nat × Nat) := [(9705220096,116497007055694,116497396966289)]
theorem point_links_checked74014 : (cuts74014.take 1).map (fun c => (9705095169-1+2*2^10*c.k,116496851514704+c.lower,116497241425197+c.upper)) = pointBounds74014 := by
 decide +kernel
def cuts74015 : List PrefixCut := [⟨64,167313732,167313831⟩]
theorem checked74015 : checkPrefixCuts (2^48) 9705226241 10 Manual.Count131072.C074015.packed 64 cuts74015 = true := by
 decide +kernel
def cuts74016 : List PrefixCut := [⟨64,165165354,165165449⟩]
theorem checked74016 : checkPrefixCuts (2^48) 9705357313 10 Manual.Count131072.C074016.packed 64 cuts74016 = true := by
 decide +kernel
def cuts74017 : List PrefixCut := [⟨18,46547515,46547538⟩,
⟨64,166642191,166642282⟩]
theorem checked74017 : checkPrefixCuts (2^48) 9705488385 10 Manual.Count131072.C074017.packed 64 cuts74017 = true := by
 decide +kernel
def pointBounds74017 : List (Nat × Nat × Nat) := [(9705525248,116497393767934,116497783678751)]
theorem point_links_checked74017 : (cuts74017.take 1).map (fun c => (9705488385-1+2*2^10*c.k,116497347220419+c.lower,116497737131213+c.upper)) = pointBounds74017 := by
 decide +kernel
def cuts74018 : List PrefixCut := [⟨64,165102879,165102979⟩]
theorem checked74018 : checkPrefixCuts (2^48) 9705619457 10 Manual.Count131072.C074018.packed 64 cuts74018 = true := by
 decide +kernel
def cuts74019 : List PrefixCut := [⟨39,98892450,98892509⟩,
⟨64,163563616,163563711⟩]
theorem checked74019 : checkPrefixCuts (2^48) 9705750529 10 Manual.Count131072.C074019.packed 64 cuts74019 = true := by
 decide +kernel
def pointBounds74019 : List (Nat × Nat × Nat) := [(9705830400,116497777857939,116498167768983)]
theorem point_links_checked74019 : (cuts74019.take 1).map (fun c => (9705750529-1+2*2^10*c.k,116497678965489+c.lower,116498068876474+c.upper)) = pointBounds74019 := by
 decide +kernel
def cuts74020 : List PrefixCut := [⟨64,165185432,165185527⟩]
theorem checked74020 : checkPrefixCuts (2^48) 9705881601 10 Manual.Count131072.C074020.packed 64 cuts74020 = true := by
 decide +kernel
def cuts74021 : List PrefixCut := [⟨60,156715297,156715390⟩,
⟨64,167677174,167677274⟩]
theorem checked74021 : checkPrefixCuts (2^48) 9706012673 10 Manual.Count131072.C074021.packed 64 cuts74021 = true := by
 decide +kernel
def pointBounds74021 : List (Nat × Nat × Nat) := [(9706135552,116498164429834,116498554341102)]
theorem point_links_checked74021 : (cuts74021.take 1).map (fun c => (9706012673-1+2*2^10*c.k,116498007714537+c.lower,116498397625712+c.upper)) = pointBounds74021 := by
 decide +kernel
def cuts74022 : List PrefixCut := [⟨64,164136979,164137068⟩]
theorem checked74022 : checkPrefixCuts (2^48) 9706143745 10 Manual.Count131072.C074022.packed 64 cuts74022 = true := by
 decide +kernel
def cuts74023 : List PrefixCut := [⟨64,164047766,164047861⟩]
theorem checked74023 : checkPrefixCuts (2^48) 9706274817 10 Manual.Count131072.C074023.packed 64 cuts74023 = true := by
 decide +kernel
def cuts74024 : List PrefixCut := [⟨17,43730232,43730259⟩,
⟨64,165495482,165495582⟩]
theorem checked74024 : checkPrefixCuts (2^48) 9706405889 10 Manual.Count131072.C074024.packed 64 cuts74024 = true := by
 decide +kernel
def pointBounds74024 : List (Nat × Nat × Nat) := [(9706440704,116498547306688,116498937218174)]
theorem point_links_checked74024 : (cuts74024.take 1).map (fun c => (9706405889-1+2*2^10*c.k,116498503576456+c.lower,116498893487915+c.upper)) = pointBounds74024 := by
 decide +kernel
def cuts74025 : List PrefixCut := [⟨64,164565317,164565415⟩]
theorem checked74025 : checkPrefixCuts (2^48) 9706536961 10 Manual.Count131072.C074025.packed 64 cuts74025 = true := by
 decide +kernel
def cuts74026 : List PrefixCut := [⟨38,99289086,99289142⟩,
⟨64,166273966,166274061⟩]
theorem checked74026 : checkPrefixCuts (2^48) 9706668033 10 Manual.Count131072.C074026.packed 64 cuts74026 = true := by
 decide +kernel
def pointBounds74026 : List (Nat × Nat × Nat) := [(9706745856,116498932926341,116499322838054)]
theorem point_links_checked74026 : (cuts74026.take 1).map (fun c => (9706668033-1+2*2^10*c.k,116498833637255+c.lower,116499223548912+c.upper)) = pointBounds74026 := by
 decide +kernel
def cuts74027 : List PrefixCut := [⟨64,166561690,166561789⟩]
theorem checked74027 : checkPrefixCuts (2^48) 9706799105 10 Manual.Count131072.C074027.packed 64 cuts74027 = true := by
 decide +kernel
def cuts74028 : List PrefixCut := [⟨59,154467728,154467820⟩,
⟨64,167342367,167342468⟩]
theorem checked74028 : checkPrefixCuts (2^48) 9706930177 10 Manual.Count131072.C074028.packed 64 cuts74028 = true := by
 decide +kernel
def pointBounds74028 : List (Nat × Nat × Nat) := [(9707051008,116499320940639,116499710852582)]
theorem point_links_checked74028 : (cuts74028.take 1).map (fun c => (9706930177-1+2*2^10*c.k,116499166472911+c.lower,116499556384762+c.upper)) = pointBounds74028 := by
 decide +kernel
def cuts74029 : List PrefixCut := [⟨64,163193565,163193658⟩]
theorem checked74029 : checkPrefixCuts (2^48) 9707061249 10 Manual.Count131072.C074029.packed 64 cuts74029 = true := by
 decide +kernel
def cuts74030 : List PrefixCut := [⟨64,167105878,167105984⟩]
theorem checked74030 : checkPrefixCuts (2^48) 9707192321 10 Manual.Count131072.C074030.packed 64 cuts74030 = true := by
 decide +kernel
def cuts74031 : List PrefixCut := [⟨16,41783366,41783389⟩,
⟨64,166784669,166784765⟩]
theorem checked74031 : checkPrefixCuts (2^48) 9707323393 10 Manual.Count131072.C074031.packed 64 cuts74031 = true := by
 decide +kernel
def pointBounds74031 : List (Nat × Nat × Nat) := [(9707356160,116499705898087,116500095810261)]
theorem point_links_checked74031 : (cuts74031.take 1).map (fun c => (9707323393-1+2*2^10*c.k,116499664114721+c.lower,116500054026872+c.upper)) = pointBounds74031 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000125
