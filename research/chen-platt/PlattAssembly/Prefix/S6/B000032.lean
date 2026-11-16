import PlattAssemblyKernel
import PlattCertificates.Count131072.C051024
import PlattCertificates.Count131072.C051025
import PlattCertificates.Count131072.C051026
import PlattCertificates.Count131072.C051027
import PlattCertificates.Count131072.C051028
import PlattCertificates.Count131072.C051029
import PlattCertificates.Count131072.C051030
import PlattCertificates.Count131072.C051031
import PlattCertificates.Count131072.C051032
import PlattCertificates.Count131072.C051033
import PlattCertificates.Count131072.C051034
import PlattCertificates.Count131072.C051035
import PlattCertificates.Count131072.C051036
import PlattCertificates.Count131072.C051037
import PlattCertificates.Count131072.C051038
import PlattCertificates.Count131072.C051039
import PlattCertificates.Count131072.C051040
import PlattCertificates.Count131072.C051041
import PlattCertificates.Count131072.C051042
import PlattCertificates.Count131072.C051043
import PlattCertificates.Count131072.C051044
import PlattCertificates.Count131072.C051045
import PlattCertificates.Count131072.C051046
import PlattCertificates.Count131072.C051047
import PlattCertificates.Count131072.C051048
import PlattCertificates.Count131072.C051049
import PlattCertificates.Count131072.C051050
import PlattCertificates.Count131072.C051051
import PlattCertificates.Count131072.C051052
import PlattCertificates.Count131072.C051053
import PlattCertificates.Count131072.C051054
import PlattCertificates.Count131072.C051055
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000032
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts51024 : List PrefixCut := [⟨1,3743604,3743606⟩,
⟨64,247958807,247958944⟩]
theorem checked51024 : checkPrefixCuts (2^48) 6691749889 10 Manual.Count131072.C051024.packed 64 cuts51024 = true := by
 decide +kernel
def pointBounds51024 : List (Nat × Nat × Nat) := [(6691751936,111909085041146,111909472306685)]
theorem point_links_checked51024 : (cuts51024.take 1).map (fun c => (6691749889-1+2*2^10*c.k,111909081297542+c.lower,111909468563079+c.upper)) = pointBounds51024 := by
 decide +kernel
def cuts51025 : List PrefixCut := [⟨40,151338684,151338767⟩,
⟨64,244757231,244757369⟩]
theorem checked51025 : checkPrefixCuts (2^48) 6691880961 10 Manual.Count131072.C051025.packed 64 cuts51025 = true := by
 decide +kernel
def pointBounds51025 : List (Nat × Nat × Nat) := [(6691962880,111909480595033,111909867860790)]
theorem point_links_checked51025 : (cuts51025.take 1).map (fun c => (6691880961-1+2*2^10*c.k,111909329256349+c.lower,111909716522023+c.upper)) = pointBounds51025 := by
 decide +kernel
def cuts51026 : List PrefixCut := [⟨64,246771392,246771532⟩]
theorem checked51026 : checkPrefixCuts (2^48) 6692012033 10 Manual.Count131072.C051026.packed 64 cuts51026 = true := by
 decide +kernel
def cuts51027 : List PrefixCut := [⟨15,56529181,56529213⟩,
⟨64,241088427,241088568⟩]
theorem checked51027 : checkPrefixCuts (2^48) 6692143105 10 Manual.Count131072.C051027.packed 64 cuts51027 = true := by
 decide +kernel
def pointBounds51027 : List (Nat × Nat × Nat) := [(6692173824,111909877314153,111910264580137)]
theorem point_links_checked51027 : (cuts51027.take 1).map (fun c => (6692143105-1+2*2^10*c.k,111909820784972+c.lower,111910208050924+c.upper)) = pointBounds51027 := by
 decide +kernel
def cuts51028 : List PrefixCut := [⟨54,203272752,203272867⟩,
⟨64,241462252,241462390⟩]
theorem checked51028 : checkPrefixCuts (2^48) 6692274177 10 Manual.Count131072.C051028.packed 64 cuts51028 = true := by
 decide +kernel
def pointBounds51028 : List (Nat × Nat × Nat) := [(6692384768,111910265146151,111910652412359)]
theorem point_links_checked51028 : (cuts51028.take 1).map (fun c => (6692274177-1+2*2^10*c.k,111910061873399+c.lower,111910449139492+c.upper)) = pointBounds51028 := by
 decide +kernel
def cuts51029 : List PrefixCut := [⟨64,242382802,242382944⟩]
theorem checked51029 : checkPrefixCuts (2^48) 6692405249 10 Manual.Count131072.C051029.packed 64 cuts51029 = true := by
 decide +kernel
def cuts51030 : List PrefixCut := [⟨29,108130718,108130780⟩,
⟨64,241831303,241831439⟩]
theorem checked51030 : checkPrefixCuts (2^48) 6692536321 10 Manual.Count131072.C051030.packed 64 cuts51030 = true := by
 decide +kernel
def pointBounds51030 : List (Nat × Nat × Nat) := [(6692595712,111910653849171,111911041115606)]
theorem point_links_checked51030 : (cuts51030.take 1).map (fun c => (6692536321-1+2*2^10*c.k,111910545718453+c.lower,111910932984826+c.upper)) = pointBounds51030 := by
 decide +kernel
def cuts51031 : List PrefixCut := [⟨64,244476152,244476289⟩]
theorem checked51031 : checkPrefixCuts (2^48) 6692667393 10 Manual.Count131072.C051031.packed 64 cuts51031 = true := by
 decide +kernel
def cuts51032 : List PrefixCut := [⟨4,15855247,15855256⟩,
⟨64,244681657,244681794⟩]
theorem checked51032 : checkPrefixCuts (2^48) 6692798465 10 Manual.Count131072.C051032.packed 64 cuts51032 = true := by
 decide +kernel
def pointBounds51032 : List (Nat × Nat × Nat) := [(6692806656,111911047881155,111911435147810)]
theorem point_links_checked51032 : (cuts51032.take 1).map (fun c => (6692798465-1+2*2^10*c.k,111911032025908+c.lower,111911419292554+c.upper)) = pointBounds51032 := by
 decide +kernel
def cuts51033 : List PrefixCut := [⟨43,166076311,166076405⟩,
⟨64,247200160,247200300⟩]
theorem checked51033 : checkPrefixCuts (2^48) 6692929537 10 Manual.Count131072.C051033.packed 64 cuts51033 = true := by
 decide +kernel
def pointBounds51033 : List (Nat × Nat × Nat) := [(6693017600,111911442783876,111911830050753)]
theorem point_links_checked51033 : (cuts51033.take 1).map (fun c => (6692929537-1+2*2^10*c.k,111911276707565+c.lower,111911663974348+c.upper)) = pointBounds51033 := by
 decide +kernel
def cuts51034 : List PrefixCut := [⟨64,242821652,242821791⟩]
theorem checked51034 : checkPrefixCuts (2^48) 6693060609 10 Manual.Count131072.C051034.packed 64 cuts51034 = true := by
 decide +kernel
def cuts51035 : List PrefixCut := [⟨18,67201970,67202007⟩,
⟨64,243700040,243700176⟩]
theorem checked51035 : checkPrefixCuts (2^48) 6693191681 10 Manual.Count131072.C051035.packed 64 cuts51035 = true := by
 decide +kernel
def pointBounds51035 : List (Nat × Nat × Nat) := [(6693228544,111911833931347,111912221198446)]
theorem point_links_checked51035 : (cuts51035.take 1).map (fun c => (6693191681-1+2*2^10*c.k,111911766729377+c.lower,111912153996439+c.upper)) = pointBounds51035 := by
 decide +kernel
def cuts51036 : List PrefixCut := [⟨57,216529483,216529604⟩,
⟨64,242181392,242181528⟩]
theorem checked51036 : checkPrefixCuts (2^48) 6693322753 10 Manual.Count131072.C051036.packed 64 cuts51036 = true := by
 decide +kernel
def pointBounds51036 : List (Nat × Nat × Nat) := [(6693439488,111912226958900,111912614226219)]
theorem point_links_checked51036 : (cuts51036.take 1).map (fun c => (6693322753-1+2*2^10*c.k,111912010429417+c.lower,111912397696615+c.upper)) = pointBounds51036 := by
 decide +kernel
def cuts51037 : List PrefixCut := [⟨64,242849447,242849587⟩]
theorem checked51037 : checkPrefixCuts (2^48) 6693453825 10 Manual.Count131072.C051037.packed 64 cuts51037 = true := by
 decide +kernel
def cuts51038 : List PrefixCut := [⟨32,122242949,122243017⟩,
⟨64,244358544,244358682⟩]
theorem checked51038 : checkPrefixCuts (2^48) 6693584897 10 Manual.Count131072.C051038.packed 64 cuts51038 = true := by
 decide +kernel
def pointBounds51038 : List (Nat × Nat × Nat) := [(6693650432,111912617703205,111913004970747)]
theorem point_links_checked51038 : (cuts51038.take 1).map (fun c => (6693584897-1+2*2^10*c.k,111912495460256+c.lower,111912882727730+c.upper)) = pointBounds51038 := by
 decide +kernel
def cuts51039 : List PrefixCut := [⟨64,246708573,246708714⟩]
theorem checked51039 : checkPrefixCuts (2^48) 6693715969 10 Manual.Count131072.C051039.packed 64 cuts51039 = true := by
 decide +kernel
def cuts51040 : List PrefixCut := [⟨7,26112896,26112911⟩,
⟨64,242835194,242835331⟩]
theorem checked51040 : checkPrefixCuts (2^48) 6693847041 10 Manual.Count131072.C051040.packed 64 cuts51040 = true := by
 decide +kernel
def pointBounds51040 : List (Nat × Nat × Nat) := [(6693861376,111913012640269,111913399908037)]
theorem point_links_checked51040 : (cuts51040.take 1).map (fun c => (6693847041-1+2*2^10*c.k,111912986527373+c.lower,111913373795126+c.upper)) = pointBounds51040 := by
 decide +kernel
def cuts51041 : List PrefixCut := [⟨46,173745123,173745221⟩,
⟨64,244974884,244975022⟩]
theorem checked51041 : checkPrefixCuts (2^48) 6693978113 10 Manual.Count131072.C051041.packed 64 cuts51041 = true := by
 decide +kernel
def pointBounds51041 : List (Nat × Nat × Nat) := [(6694072320,111913403107690,111913790375678)]
theorem point_links_checked51041 : (cuts51041.take 1).map (fun c => (6693978113-1+2*2^10*c.k,111913229362567+c.lower,111913616630457+c.upper)) = pointBounds51041 := by
 decide +kernel
def cuts51042 : List PrefixCut := [⟨64,243876867,243877000⟩]
theorem checked51042 : checkPrefixCuts (2^48) 6694109185 10 Manual.Count131072.C051042.packed 64 cuts51042 = true := by
 decide +kernel
def cuts51043 : List PrefixCut := [⟨21,78207770,78207818⟩,
⟨64,239919687,239919829⟩]
theorem checked51043 : checkPrefixCuts (2^48) 6694240257 10 Manual.Count131072.C051043.packed 64 cuts51043 = true := by
 decide +kernel
def pointBounds51043 : List (Nat × Nat × Nat) := [(6694283264,111913796422088,111914183690297)]
theorem point_links_checked51043 : (cuts51043.take 1).map (fun c => (6694240257-1+2*2^10*c.k,111913718214318+c.lower,111914105482479+c.upper)) = pointBounds51043 := by
 decide +kernel
def cuts51044 : List PrefixCut := [⟨60,227974057,227974188⟩,
⟨64,243362785,243362925⟩]
theorem checked51044 : checkPrefixCuts (2^48) 6694371329 10 Manual.Count131072.C051044.packed 64 cuts51044 = true := by
 decide +kernel
def pointBounds51044 : List (Nat × Nat × Nat) := [(6694494208,111914186108062,111914573376496)]
theorem point_links_checked51044 : (cuts51044.take 1).map (fun c => (6694371329-1+2*2^10*c.k,111913958134005+c.lower,111914345402308+c.upper)) = pointBounds51044 := by
 decide +kernel
def cuts51045 : List PrefixCut := [⟨64,244787542,244787682⟩]
theorem checked51045 : checkPrefixCuts (2^48) 6694502401 10 Manual.Count131072.C051045.packed 64 cuts51045 = true := by
 decide +kernel
def cuts51046 : List PrefixCut := [⟨35,131389478,131389552⟩,
⟨64,241797596,241797733⟩]
theorem checked51046 : checkPrefixCuts (2^48) 6694633473 10 Manual.Count131072.C051046.packed 64 cuts51046 = true := by
 decide +kernel
def pointBounds51046 : List (Nat × Nat × Nat) := [(6694705152,111914577673810,111914964942467)]
theorem point_links_checked51046 : (cuts51046.take 1).map (fun c => (6694633473-1+2*2^10*c.k,111914446284332+c.lower,111914833552915+c.upper)) = pointBounds51046 := by
 decide +kernel
def cuts51047 : List PrefixCut := [⟨64,242339434,242339573⟩]
theorem checked51047 : checkPrefixCuts (2^48) 6694764545 10 Manual.Count131072.C051047.packed 64 cuts51047 = true := by
 decide +kernel
def cuts51048 : List PrefixCut := [⟨10,37376355,37376376⟩,
⟨64,242797158,242797300⟩]
theorem checked51048 : checkPrefixCuts (2^48) 6694895617 10 Manual.Count131072.C051048.packed 64 cuts51048 = true := by
 decide +kernel
def pointBounds51048 : List (Nat × Nat × Nat) := [(6694916096,111914967797717,111915355066597)]
theorem point_links_checked51048 : (cuts51048.take 1).map (fun c => (6694895617-1+2*2^10*c.k,111914930421362+c.lower,111915317690221+c.upper)) = pointBounds51048 := by
 decide +kernel
def cuts51049 : List PrefixCut := [⟨49,187970105,187970209⟩,
⟨64,244516135,244516273⟩]
theorem checked51049 : checkPrefixCuts (2^48) 6695026689 10 Manual.Count131072.C051049.packed 64 cuts51049 = true := by
 decide +kernel
def pointBounds51049 : List (Nat × Nat × Nat) := [(6695127040,111915361188625,111915748457730)]
theorem point_links_checked51049 : (cuts51049.take 1).map (fun c => (6695026689-1+2*2^10*c.k,111915173218520+c.lower,111915560487521+c.upper)) = pointBounds51049 := by
 decide +kernel
def cuts51050 : List PrefixCut := [⟨64,245057905,245058047⟩]
theorem checked51050 : checkPrefixCuts (2^48) 6695157761 10 Manual.Count131072.C051050.packed 64 cuts51050 = true := by
 decide +kernel
def cuts51051 : List PrefixCut := [⟨24,92237045,92237098⟩,
⟨64,243581677,243581817⟩]
theorem checked51051 : checkPrefixCuts (2^48) 6695288833 10 Manual.Count131072.C051051.packed 64 cuts51051 = true := by
 decide +kernel
def pointBounds51051 : List (Nat × Nat × Nat) := [(6695337984,111915755029605,111916142298939)]
theorem point_links_checked51051 : (cuts51051.take 1).map (fun c => (6695288833-1+2*2^10*c.k,111915662792560+c.lower,111916050061841+c.upper)) = pointBounds51051 := by
 decide +kernel
def cuts51052 : List PrefixCut := [⟨63,236682449,236682589⟩,
⟨64,240213733,240213875⟩]
theorem checked51052 : checkPrefixCuts (2^48) 6695419905 10 Manual.Count131072.C051052.packed 64 cuts51052 = true := by
 decide +kernel
def pointBounds51052 : List (Nat × Nat × Nat) := [(6695548928,111916143056686,111916530326247)]
theorem point_links_checked51052 : (cuts51052.take 1).map (fun c => (6695419905-1+2*2^10*c.k,111915906374237+c.lower,111916293643658+c.upper)) = pointBounds51052 := by
 decide +kernel
def cuts51053 : List PrefixCut := [⟨64,245632005,245632150⟩]
theorem checked51053 : checkPrefixCuts (2^48) 6695550977 10 Manual.Count131072.C051053.packed 64 cuts51053 = true := by
 decide +kernel
def cuts51054 : List PrefixCut := [⟨38,144442664,144442747⟩,
⟨64,242642535,242642672⟩]
theorem checked51054 : checkPrefixCuts (2^48) 6695682049 10 Manual.Count131072.C051054.packed 64 cuts51054 = true := by
 decide +kernel
def pointBounds51054 : List (Nat × Nat × Nat) := [(6695759872,111916536662639,111916923932430)]
theorem point_links_checked51054 : (cuts51054.take 1).map (fun c => (6695682049-1+2*2^10*c.k,111916392219975+c.lower,111916779489683+c.upper)) = pointBounds51054 := by
 decide +kernel
def cuts51055 : List PrefixCut := [⟨64,242469639,242469774⟩]
theorem checked51055 : checkPrefixCuts (2^48) 6695813121 10 Manual.Count131072.C051055.packed 64 cuts51055 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000032
