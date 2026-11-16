import PlattAssemblyKernel
import PlattCertificates.Count131072.C036016
import PlattCertificates.Count131072.C036017
import PlattCertificates.Count131072.C036018
import PlattCertificates.Count131072.C036019
import PlattCertificates.Count131072.C036020
import PlattCertificates.Count131072.C036021
import PlattCertificates.Count131072.C036022
import PlattCertificates.Count131072.C036023
import PlattCertificates.Count131072.C036024
import PlattCertificates.Count131072.C036025
import PlattCertificates.Count131072.C036026
import PlattCertificates.Count131072.C036027
import PlattCertificates.Count131072.C036028
import PlattCertificates.Count131072.C036029
import PlattCertificates.Count131072.C036030
import PlattCertificates.Count131072.C036031
import PlattCertificates.Count131072.C036032
import PlattCertificates.Count131072.C036033
import PlattCertificates.Count131072.C036034
import PlattCertificates.Count131072.C036035
import PlattCertificates.Count131072.C036036
import PlattCertificates.Count131072.C036037
import PlattCertificates.Count131072.C036038
import PlattCertificates.Count131072.C036039
import PlattCertificates.Count131072.C036040
import PlattCertificates.Count131072.C036041
import PlattCertificates.Count131072.C036042
import PlattCertificates.Count131072.C036043
import PlattCertificates.Count131072.C036044
import PlattCertificates.Count131072.C036045
import PlattCertificates.Count131072.C036046
import PlattCertificates.Count131072.C036047
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000188
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts36016 : List PrefixCut := [⟨16,89185233,89185290⟩,
⟨64,345060477,345060700⟩]
theorem checked36016 : checkPrefixCuts (2^48) 4724621313 10 Manual.Count131072.C036016.packed 64 cuts36016 = true := by
 decide +kernel
def pointBounds36016 : List (Nat × Nat × Nat) := [(4724654080,107544817284714,107545201991350)]
theorem point_links_checked36016 : (cuts36016.take 1).map (fun c => (4724621313-1+2*2^10*c.k,107544728099481+c.lower,107545112806060+c.upper)) = pointBounds36016 := by
 decide +kernel
def cuts36017 : List PrefixCut := [⟨25,134935577,134935661⟩,
⟨64,349816765,349816978⟩]
theorem checked36017 : checkPrefixCuts (2^48) 4724752385 10 Manual.Count131072.C036017.packed 64 cuts36017 = true := by
 decide +kernel
def pointBounds36017 : List (Nat × Nat × Nat) := [(4724803584,107545208095535,107545592802421)]
theorem point_links_checked36017 : (cuts36017.take 1).map (fun c => (4724752385-1+2*2^10*c.k,107545073159958+c.lower,107545457866760+c.upper)) = pointBounds36017 := by
 decide +kernel
def cuts36018 : List PrefixCut := [⟨34,192359378,192359496⟩,
⟨64,353679294,353679515⟩]
theorem checked36018 : checkPrefixCuts (2^48) 4724883457 10 Manual.Count131072.C036018.packed 64 cuts36018 = true := by
 decide +kernel
def pointBounds36018 : List (Nat × Nat × Nat) := [(4724953088,107545615336101,107546000043234)]
theorem point_links_checked36018 : (cuts36018.take 1).map (fun c => (4724883457-1+2*2^10*c.k,107545422976723+c.lower,107545807683738+c.upper)) = pointBounds36018 := by
 decide +kernel
def cuts36019 : List PrefixCut := [⟨43,237627388,237627532⟩,
⟨64,350512238,350512451⟩]
theorem checked36019 : checkPrefixCuts (2^48) 4725014529 10 Manual.Count131072.C036019.packed 64 cuts36019 = true := by
 decide +kernel
def pointBounds36019 : List (Nat × Nat × Nat) := [(4725102592,107546014283405,107546398990785)]
theorem point_links_checked36019 : (cuts36019.take 1).map (fun c => (4725014529-1+2*2^10*c.k,107545776656017+c.lower,107546161363253+c.upper)) = pointBounds36019 := by
 decide +kernel
def cuts36020 : List PrefixCut := [⟨52,284620174,284620347⟩,
⟨64,351634257,351634471⟩]
theorem checked36020 : checkPrefixCuts (2^48) 4725145601 10 Manual.Count131072.C036020.packed 64 cuts36020 = true := by
 decide +kernel
def pointBounds36020 : List (Nat × Nat × Nat) := [(4725252096,107546411788429,107546796496051)]
theorem point_links_checked36020 : (cuts36020.take 1).map (fun c => (4725145601-1+2*2^10*c.k,107546127168255+c.lower,107546511875704+c.upper)) = pointBounds36020 := by
 decide +kernel
def cuts36021 : List PrefixCut := [⟨61,332265422,332265623⟩,
⟨64,349599216,349599428⟩]
theorem checked36021 : checkPrefixCuts (2^48) 4725276673 10 Manual.Count131072.C036021.packed 64 cuts36021 = true := by
 decide +kernel
def pointBounds36021 : List (Nat × Nat × Nat) := [(4725401600,107546811067934,107547195775798)]
theorem point_links_checked36021 : (cuts36021.take 1).map (fun c => (4725276673-1+2*2^10*c.k,107546478802512+c.lower,107546863510175+c.upper)) = pointBounds36021 := by
 decide +kernel
def cuts36022 : List PrefixCut := [⟨64,349470457,349470671⟩]
theorem checked36022 : checkPrefixCuts (2^48) 4725407745 10 Manual.Count131072.C036022.packed 64 cuts36022 = true := by
 decide +kernel
def cuts36023 : List PrefixCut := [⟨6,31330945,31330966⟩,
⟨64,349460735,349460944⟩]
theorem checked36023 : checkPrefixCuts (2^48) 4725538817 10 Manual.Count131072.C036023.packed 64 cuts36023 = true := by
 decide +kernel
def pointBounds36023 : List (Nat × Nat × Nat) := [(4725551104,107547209203130,107547593911240)]
theorem point_links_checked36023 : (cuts36023.take 1).map (fun c => (4725538817-1+2*2^10*c.k,107547177872185+c.lower,107547562580274+c.upper)) = pointBounds36023 := by
 decide +kernel
def cuts36024 : List PrefixCut := [⟨15,80111923,80111972⟩,
⟨64,342958783,342958995⟩]
theorem checked36024 : checkPrefixCuts (2^48) 4725669889 10 Manual.Count131072.C036024.packed 64 cuts36024 = true := by
 decide +kernel
def pointBounds36024 : List (Nat × Nat × Nat) := [(4725700608,107547607444843,107547992153190)]
theorem point_links_checked36024 : (cuts36024.take 1).map (fun c => (4725669889-1+2*2^10*c.k,107547527332920+c.lower,107547912041218+c.upper)) = pointBounds36024 := by
 decide +kernel
def cuts36025 : List PrefixCut := [⟨24,132821023,132821104⟩,
⟨64,349977405,349977622⟩]
theorem checked36025 : checkPrefixCuts (2^48) 4725800961 10 Manual.Count131072.C036025.packed 64 cuts36025 = true := by
 decide +kernel
def pointBounds36025 : List (Nat × Nat × Nat) := [(4725850112,107548003112726,107548387821317)]
theorem point_links_checked36025 : (cuts36025.take 1).map (fun c => (4725800961-1+2*2^10*c.k,107547870291703+c.lower,107548255000213+c.upper)) = pointBounds36025 := by
 decide +kernel
def cuts36026 : List PrefixCut := [⟨33,181417415,181417527⟩,
⟨64,352647825,352648041⟩]
theorem checked36026 : checkPrefixCuts (2^48) 4725932033 10 Manual.Count131072.C036026.packed 64 cuts36026 = true := by
 decide +kernel
def pointBounds36026 : List (Nat × Nat × Nat) := [(4725999616,107548401686523,107548786395362)]
theorem point_links_checked36026 : (cuts36026.take 1).map (fun c => (4725932033-1+2*2^10*c.k,107548220269108+c.lower,107548604977835+c.upper)) = pointBounds36026 := by
 decide +kernel
def cuts36027 : List PrefixCut := [⟨42,230130021,230130169⟩,
⟨64,351030002,351030223⟩]
theorem checked36027 : checkPrefixCuts (2^48) 4726063105 10 Manual.Count131072.C036027.packed 64 cuts36027 = true := by
 decide +kernel
def pointBounds36027 : List (Nat × Nat × Nat) := [(4726149120,107548803046954,107549187756045)]
theorem point_links_checked36027 : (cuts36027.take 1).map (fun c => (4726063105-1+2*2^10*c.k,107548572916933+c.lower,107548957625876+c.upper)) = pointBounds36027 := by
 decide +kernel
def cuts36028 : List PrefixCut := [⟨51,281043305,281043478⟩,
⟨64,353819353,353819571⟩]
theorem checked36028 : checkPrefixCuts (2^48) 4726194177 10 Manual.Count131072.C036028.packed 64 cuts36028 = true := by
 decide +kernel
def pointBounds36028 : List (Nat × Nat × Nat) := [(4726298624,107549204990240,107549589699577)]
theorem point_links_checked36028 : (cuts36028.take 1).map (fun c => (4726194177-1+2*2^10*c.k,107548923946935+c.lower,107549308656099+c.upper)) = pointBounds36028 := by
 decide +kernel
def cuts36029 : List PrefixCut := [⟨60,329928751,329928952⟩,
⟨64,352439822,352440037⟩]
theorem checked36029 : checkPrefixCuts (2^48) 4726325249 10 Manual.Count131072.C036029.packed 64 cuts36029 = true := by
 decide +kernel
def pointBounds36029 : List (Nat × Nat × Nat) := [(4726448128,107549607695039,107549992404622)]
theorem point_links_checked36029 : (cuts36029.take 1).map (fun c => (4726325249-1+2*2^10*c.k,107549277766288+c.lower,107549662475670+c.upper)) = pointBounds36029 := by
 decide +kernel
def cuts36030 : List PrefixCut := [⟨64,351655908,351656124⟩]
theorem checked36030 : checkPrefixCuts (2^48) 4726456321 10 Manual.Count131072.C036030.packed 64 cuts36030 = true := by
 decide +kernel
def cuts36031 : List PrefixCut := [⟨5,26440793,26440809⟩,
⟨64,349800048,349800263⟩]
theorem checked36031 : checkPrefixCuts (2^48) 4726587393 10 Manual.Count131072.C036031.packed 64 cuts36031 = true := by
 decide +kernel
def pointBounds36031 : List (Nat × Nat × Nat) := [(4726597632,107550008302811,107550393012640)]
theorem point_links_checked36031 : (cuts36031.take 1).map (fun c => (4726587393-1+2*2^10*c.k,107549981862018+c.lower,107550366571831+c.upper)) = pointBounds36031 := by
 decide +kernel
def cuts36032 : List PrefixCut := [⟨14,78605430,78605478⟩,
⟨64,349849930,349850141⟩]
theorem checked36032 : checkPrefixCuts (2^48) 4726718465 10 Manual.Count131072.C036032.packed 64 cuts36032 = true := by
 decide +kernel
def pointBounds36032 : List (Nat × Nat × Nat) := [(4726747136,107550410267496,107550794977572)]
theorem point_links_checked36032 : (cuts36032.take 1).map (fun c => (4726718465-1+2*2^10*c.k,107550331662066+c.lower,107550716372094+c.upper)) = pointBounds36032 := by
 decide +kernel
def cuts36033 : List PrefixCut := [⟨23,125169478,125169557⟩,
⟨64,349363851,349364072⟩]
theorem checked36033 : checkPrefixCuts (2^48) 4726849537 10 Manual.Count131072.C036033.packed 64 cuts36033 = true := by
 decide +kernel
def pointBounds36033 : List (Nat × Nat × Nat) := [(4726896640,107550806681474,107551191391792)]
theorem point_links_checked36033 : (cuts36033.take 1).map (fun c => (4726849537-1+2*2^10*c.k,107550681511996+c.lower,107551066222235+c.upper)) = pointBounds36033 := by
 decide +kernel
def cuts36034 : List PrefixCut := [⟨32,178280823,178280931⟩,
⟨64,355785086,355785303⟩]
theorem checked36034 : checkPrefixCuts (2^48) 4726980609 10 Manual.Count131072.C036034.packed 64 cuts36034 = true := by
 decide +kernel
def pointBounds36034 : List (Nat × Nat × Nat) := [(4727046144,107551209156670,107551593867238)]
theorem point_links_checked36034 : (cuts36034.take 1).map (fun c => (4726980609-1+2*2^10*c.k,107551030875847+c.lower,107551415586307+c.upper)) = pointBounds36034 := by
 decide +kernel
def cuts36035 : List PrefixCut := [⟨41,227399525,227399668⟩,
⟨64,352143023,352143240⟩]
theorem checked36035 : checkPrefixCuts (2^48) 4727111681 10 Manual.Count131072.C036035.packed 64 cuts36035 = true := by
 decide +kernel
def pointBounds36035 : List (Nat × Nat × Nat) := [(4727195648,107551614060458,107551998771278)]
theorem point_links_checked36035 : (cuts36035.take 1).map (fun c => (4727111681-1+2*2^10*c.k,107551386660933+c.lower,107551771371610+c.upper)) = pointBounds36035 := by
 decide +kernel
def cuts36036 : List PrefixCut := [⟨50,273300082,273300247⟩,
⟨64,351001968,351002179⟩]
theorem checked36036 : checkPrefixCuts (2^48) 4727242753 10 Manual.Count131072.C036036.packed 64 cuts36036 = true := by
 decide +kernel
def pointBounds36036 : List (Nat × Nat × Nat) := [(4727345152,107552012104038,107552396815097)]
theorem point_links_checked36036 : (cuts36036.take 1).map (fun c => (4727242753-1+2*2^10*c.k,107551738803956+c.lower,107552123514850+c.upper)) = pointBounds36036 := by
 decide +kernel
def cuts36037 : List PrefixCut := [⟨59,325092381,325092582⟩,
⟨64,353373837,353374054⟩]
theorem checked36037 : checkPrefixCuts (2^48) 4727373825 10 Manual.Count131072.C036037.packed 64 cuts36037 = true := by
 decide +kernel
def pointBounds36037 : List (Nat × Nat × Nat) := [(4727494656,107552414898305,107552799609611)]
theorem point_links_checked36037 : (cuts36037.take 1).map (fun c => (4727373825-1+2*2^10*c.k,107552089805924+c.lower,107552474517029+c.upper)) = pointBounds36037 := by
 decide +kernel
def cuts36038 : List PrefixCut := [⟨64,348898652,348898873⟩]
theorem checked36038 : checkPrefixCuts (2^48) 4727504897 10 Manual.Count131072.C036038.packed 64 cuts36038 = true := by
 decide +kernel
def cuts36039 : List PrefixCut := [⟨4,21374191,21374206⟩,
⟨64,348888988,348889202⟩]
theorem checked36039 : checkPrefixCuts (2^48) 4727635969 10 Manual.Count131072.C036039.packed 64 cuts36039 = true := by
 decide +kernel
def pointBounds36039 : List (Nat × Nat × Nat) := [(4727644160,107552813452604,107553198164162)]
theorem point_links_checked36039 : (cuts36039.take 1).map (fun c => (4727635969-1+2*2^10*c.k,107552792078413+c.lower,107553176789956+c.upper)) = pointBounds36039 := by
 decide +kernel
def cuts36040 : List PrefixCut := [⟨13,69895700,69895745⟩,
⟨64,355428191,355428407⟩]
theorem checked36040 : checkPrefixCuts (2^48) 4727767041 10 Manual.Count131072.C036040.packed 64 cuts36040 = true := by
 decide +kernel
def pointBounds36040 : List (Nat × Nat × Nat) := [(4727793664,107553210863101,107553595574903)]
theorem point_links_checked36040 : (cuts36040.take 1).map (fun c => (4727767041-1+2*2^10*c.k,107553140967401+c.lower,107553525679158+c.upper)) = pointBounds36040 := by
 decide +kernel
def cuts36041 : List PrefixCut := [⟨22,120617103,120617178⟩,
⟨64,356430390,356430613⟩]
theorem checked36041 : checkPrefixCuts (2^48) 4727898113 10 Manual.Count131072.C036041.packed 64 cuts36041 = true := by
 decide +kernel
def pointBounds36041 : List (Nat × Nat × Nat) := [(4727943168,107553617012695,107554001724743)]
theorem point_links_checked36041 : (cuts36041.take 1).map (fun c => (4727898113-1+2*2^10*c.k,107553496395592+c.lower,107553881107565+c.upper)) = pointBounds36041 := by
 decide +kernel
def cuts36042 : List PrefixCut := [⟨31,170502061,170502163⟩,
⟨64,349812495,349812707⟩]
theorem checked36042 : checkPrefixCuts (2^48) 4728029185 10 Manual.Count131072.C036042.packed 64 cuts36042 = true := by
 decide +kernel
def pointBounds36042 : List (Nat × Nat × Nat) := [(4728092672,107554023328043,107554408040341)]
theorem point_links_checked36042 : (cuts36042.take 1).map (fun c => (4728029185-1+2*2^10*c.k,107553852825982+c.lower,107554237538178+c.upper)) = pointBounds36042 := by
 decide +kernel
def cuts36043 : List PrefixCut := [⟨40,216038256,216038389⟩,
⟨64,347064328,347064542⟩]
theorem checked36043 : checkPrefixCuts (2^48) 4728160257 10 Manual.Count131072.C036043.packed 64 cuts36043 = true := by
 decide +kernel
def pointBounds36043 : List (Nat × Nat × Nat) := [(4728242176,107554418676733,107554803389274)]
theorem point_links_checked36043 : (cuts36043.take 1).map (fun c => (4728160257-1+2*2^10*c.k,107554202638477+c.lower,107554587350885+c.upper)) = pointBounds36043 := by
 decide +kernel
def cuts36044 : List PrefixCut := [⟨49,267703281,267703445⟩,
⟨64,349197776,349197989⟩]
theorem checked36044 : checkPrefixCuts (2^48) 4728291329 10 Manual.Count131072.C036044.packed 64 cuts36044 = true := by
 decide +kernel
def pointBounds36044 : List (Nat × Nat × Nat) := [(4728391680,107554817406086,107555202118872)]
theorem point_links_checked36044 : (cuts36044.take 1).map (fun c => (4728291329-1+2*2^10*c.k,107554549702805+c.lower,107554934415427+c.upper)) = pointBounds36044 := by
 decide +kernel
def cuts36045 : List PrefixCut := [⟨58,317936601,317936795⟩,
⟨64,353235943,353236159⟩]
theorem checked36045 : checkPrefixCuts (2^48) 4728422401 10 Manual.Count131072.C036045.packed 64 cuts36045 = true := by
 decide +kernel
def pointBounds36045 : List (Nat × Nat × Nat) := [(4728541184,107555216837182,107555601550211)]
theorem point_links_checked36045 : (cuts36045.take 1).map (fun c => (4728422401-1+2*2^10*c.k,107554898900581+c.lower,107555283613416+c.upper)) = pointBounds36045 := by
 decide +kernel
def cuts36046 : List PrefixCut := [⟨64,348999827,349000043⟩]
theorem checked36046 : checkPrefixCuts (2^48) 4728553473 10 Manual.Count131072.C036046.packed 64 cuts36046 = true := by
 decide +kernel
def cuts36047 : List PrefixCut := [⟨3,16547936,16547946⟩,
⟨64,348454415,348454634⟩]
theorem checked36047 : checkPrefixCuts (2^48) 4728684545 10 Manual.Count131072.C036047.packed 64 cuts36047 = true := by
 decide +kernel
def pointBounds36047 : List (Nat × Nat × Nat) := [(4728690688,107555617684287,107556002397564)]
theorem point_links_checked36047 : (cuts36047.take 1).map (fun c => (4728684545-1+2*2^10*c.k,107555601136351+c.lower,107555985849618+c.upper)) = pointBounds36047 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000188
