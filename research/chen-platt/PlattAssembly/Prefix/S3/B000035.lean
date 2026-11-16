import PlattAssemblyKernel
import PlattCertificates.Count131072.C021120
import PlattCertificates.Count131072.C021121
import PlattCertificates.Count131072.C021122
import PlattCertificates.Count131072.C021123
import PlattCertificates.Count131072.C021124
import PlattCertificates.Count131072.C021125
import PlattCertificates.Count131072.C021126
import PlattCertificates.Count131072.C021127
import PlattCertificates.Count131072.C021128
import PlattCertificates.Count131072.C021129
import PlattCertificates.Count131072.C021130
import PlattCertificates.Count131072.C021131
import PlattCertificates.Count131072.C021132
import PlattCertificates.Count131072.C021133
import PlattCertificates.Count131072.C021134
import PlattCertificates.Count131072.C021135
import PlattCertificates.Count131072.C021136
import PlattCertificates.Count131072.C021137
import PlattCertificates.Count131072.C021138
import PlattCertificates.Count131072.C021139
import PlattCertificates.Count131072.C021140
import PlattCertificates.Count131072.C021141
import PlattCertificates.Count131072.C021142
import PlattCertificates.Count131072.C021143
import PlattCertificates.Count131072.C021144
import PlattCertificates.Count131072.C021145
import PlattCertificates.Count131072.C021146
import PlattCertificates.Count131072.C021147
import PlattCertificates.Count131072.C021148
import PlattCertificates.Count131072.C021149
import PlattCertificates.Count131072.C021150
import PlattCertificates.Count131072.C021151
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000035
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts21120 : List PrefixCut := [⟨71,338109873,338110067⟩,
⟨128,613058814,613059159⟩]
theorem checked21120 : checkPrefixCuts (2^48) 2772172801 9 Manual.Count131072.C021120.packed 128 cuts21120 = true := by
 decide +kernel
def pointBounds21120 : List (Nat × Nat × Nat) := [(2772245504,100726332181965,100726712962998)]
theorem point_links_checked21120 : (cuts21120.take 1).map (fun c => (2772172801-1+2*2^9*c.k,100725994072092+c.lower,100726374852931+c.upper)) = pointBounds21120 := by
 decide +kernel
def cuts21121 : List PrefixCut := [⟨28,133411091,133411170⟩,
⟨113,540438424,540438735⟩,
⟨128,611405462,611405814⟩]
theorem checked21121 : checkPrefixCuts (2^48) 2772303873 9 Manual.Count131072.C021121.packed 128 cuts21121 = true := by
 decide +kernel
def pointBounds21121 : List (Nat × Nat × Nat) := [(2772332544,100726740541997,100727121323260),(2772419584,100727147569330,100727528350825)]
theorem point_links_checked21121 : (cuts21121.take 2).map (fun c => (2772303873-1+2*2^9*c.k,100726607130906+c.lower,100726987912090+c.upper)) = pointBounds21121 := by
 decide +kernel
def cuts21122 : List PrefixCut := [⟨70,338991770,338991966⟩,
⟨128,619498521,619498878⟩]
theorem checked21122 : checkPrefixCuts (2^48) 2772434945 9 Manual.Count131072.C021122.packed 128 cuts21122 = true := by
 decide +kernel
def pointBounds21122 : List (Nat × Nat × Nat) := [(2772506624,100727557528138,100727938309870)]
theorem point_links_checked21122 : (cuts21122.take 1).map (fun c => (2772434945-1+2*2^9*c.k,100727218536368+c.lower,100727599317904+c.upper)) = pointBounds21122 := by
 decide +kernel
def cuts21123 : List PrefixCut := [⟨27,129337681,129337757⟩,
⟨112,536225188,536225501⟩,
⟨128,612972006,612972360⟩]
theorem checked21123 : checkPrefixCuts (2^48) 2772566017 9 Manual.Count131072.C021123.packed 128 cuts21123 = true := by
 decide +kernel
def pointBounds21123 : List (Nat × Nat × Nat) := [(2772593664,100727967372570,100728348154539),(2772680704,100728374260077,100728755042283)]
theorem point_links_checked21123 : (cuts21123.take 2).map (fun c => (2772566017-1+2*2^9*c.k,100727838034889+c.lower,100728218816782+c.upper)) = pointBounds21123 := by
 decide +kernel
def cuts21124 : List PrefixCut := [⟨69,331244575,331244765⟩,
⟨128,612943014,612943372⟩]
theorem checked21124 : checkPrefixCuts (2^48) 2772697089 9 Manual.Count131072.C021124.packed 128 cuts21124 = true := by
 decide +kernel
def pointBounds21124 : List (Nat × Nat × Nat) := [(2772767744,100728782251470,100729163033907)]
theorem point_links_checked21124 : (cuts21124.take 1).map (fun c => (2772697089-1+2*2^9*c.k,100728451006895+c.lower,100728831789142+c.upper)) = pointBounds21124 := by
 decide +kernel
def cuts21125 : List PrefixCut := [⟨26,120290960,120291027⟩,
⟨111,525312946,525313242⟩,
⟨128,605503762,605504105⟩]
theorem checked21125 : checkPrefixCuts (2^48) 2772828161 9 Manual.Count131072.C021125.packed 128 cuts21125 = true := by
 decide +kernel
def pointBounds21125 : List (Nat × Nat × Nat) := [(2772854784,100729184240869,100729565023541),(2772941824,100729589262855,100729970045756)]
theorem point_links_checked21125 : (cuts21125.take 2).map (fun c => (2772828161-1+2*2^9*c.k,100729063949909+c.lower,100729444732514+c.upper)) = pointBounds21125 := by
 decide +kernel
def cuts21126 : List PrefixCut := [⟨68,326848559,326848749⟩,
⟨128,615422655,615423014⟩]
theorem checked21126 : checkPrefixCuts (2^48) 2772959233 9 Manual.Count131072.C021126.packed 128 cuts21126 = true := by
 decide +kernel
def pointBounds21126 : List (Nat × Nat × Nat) := [(2773028864,100729996302230,100730377085368)]
theorem point_links_checked21126 : (cuts21126.take 1).map (fun c => (2772959233-1+2*2^9*c.k,100729669453671+c.lower,100730050236619+c.upper)) = pointBounds21126 := by
 decide +kernel
def cuts21127 : List PrefixCut := [⟨25,121294627,121294695⟩,
⟨110,526786018,526786321⟩,
⟨128,609405226,609405576⟩]
theorem checked21127 : checkPrefixCuts (2^48) 2773090305 9 Manual.Count131072.C021127.packed 128 cuts21127 = true := by
 decide +kernel
def pointBounds21127 : List (Nat × Nat × Nat) := [(2773115904,100730406170953,100730786954328),(2773202944,100730811662344,100731192445954)]
theorem point_links_checked21127 : (cuts21127.take 2).map (fun c => (2773090305-1+2*2^9*c.k,100730284876326+c.lower,100730665659633+c.upper)) = pointBounds21127 := by
 decide +kernel
def cuts21128 : List PrefixCut := [⟨67,323975911,323976097⟩,
⟨128,617089991,617090349⟩]
theorem checked21128 : checkPrefixCuts (2^48) 2773221377 9 Manual.Count131072.C021128.packed 128 cuts21128 = true := by
 decide +kernel
def pointBounds21128 : List (Nat × Nat × Nat) := [(2773289984,100731218257463,100731599041306)]
theorem point_links_checked21128 : (cuts21128.take 1).map (fun c => (2773221377-1+2*2^9*c.k,100730894281552+c.lower,100731275065209+c.upper)) = pointBounds21128 := by
 decide +kernel
def cuts21129 : List PrefixCut := [⟨24,113874243,113874309⟩,
⟨109,520849768,520850068⟩,
⟨128,612087669,612088018⟩]
theorem checked21129 : checkPrefixCuts (2^48) 2773352449 9 Manual.Count131072.C021129.packed 128 cuts21129 = true := by
 decide +kernel
def pointBounds21129 : List (Nat × Nat × Nat) := [(2773377024,100731625245786,100732006029867),(2773464064,100732032221311,100732413005626)]
theorem point_links_checked21129 : (cuts21129.take 2).map (fun c => (2773352449-1+2*2^9*c.k,100731511371543+c.lower,100731892155558+c.upper)) = pointBounds21129 := by
 decide +kernel
def cuts21130 : List PrefixCut := [⟨66,316739698,316739887⟩,
⟨128,614595882,614596238⟩]
theorem checked21130 : checkPrefixCuts (2^48) 2773483521 9 Manual.Count131072.C021130.packed 128 cuts21130 = true := by
 decide +kernel
def pointBounds21130 : List (Nat × Nat × Nat) := [(2773551104,100732440198910,100732820983463)]
theorem point_links_checked21130 : (cuts21130.take 1).map (fun c => (2773483521-1+2*2^9*c.k,100732123459212+c.lower,100732504243576+c.upper)) = pointBounds21130 := by
 decide +kernel
def cuts21131 : List PrefixCut := [⟨23,112036830,112036891⟩,
⟨108,515929637,515929934⟩,
⟨128,611421034,611421388⟩]
theorem checked21131 : checkPrefixCuts (2^48) 2773614593 9 Manual.Count131072.C021131.packed 128 cuts21131 = true := by
 decide +kernel
def pointBounds21131 : List (Nat × Nat × Nat) := [(2773638144,100732850091924,100733230876705),(2773725184,100733253984731,100733634769748)]
theorem point_links_checked21131 : (cuts21131.take 2).map (fun c => (2773614593-1+2*2^9*c.k,100732738055094+c.lower,100733118839814+c.upper)) = pointBounds21131 := by
 decide +kernel
def cuts21132 : List PrefixCut := [⟨65,307678402,307678580⟩,
⟨128,606927117,606927471⟩]
theorem checked21132 : checkPrefixCuts (2^48) 2773745665 9 Manual.Count131072.C021132.packed 128 cuts21132 = true := by
 decide +kernel
def pointBounds21132 : List (Nat × Nat × Nat) := [(2773812224,100733657154530,100734037939782)]
theorem point_links_checked21132 : (cuts21132.take 1).map (fun c => (2773745665-1+2*2^9*c.k,100733349476128+c.lower,100733730261202+c.upper)) = pointBounds21132 := by
 decide +kernel
def cuts21133 : List PrefixCut := [⟨22,105734931,105734994⟩,
⟨107,506139678,506139973⟩,
⟨128,606391131,606391481⟩]
theorem checked21133 : checkPrefixCuts (2^48) 2773876737 9 Manual.Count131072.C021133.packed 128 cuts21133 = true := by
 decide +kernel
def pointBounds21133 : List (Nat × Nat × Nat) := [(2773899264,100734062138176,100734442923667),(2773986304,100734462542923,100734843328646)]
theorem point_links_checked21133 : (cuts21133.take 2).map (fun c => (2773876737-1+2*2^9*c.k,100733956403245+c.lower,100734337188673+c.upper)) = pointBounds21133 := by
 decide +kernel
def cuts21134 : List PrefixCut := [⟨64,305315618,305315795⟩,
⟨128,611232825,611233175⟩]
theorem checked21134 : checkPrefixCuts (2^48) 2774007809 9 Manual.Count131072.C021134.packed 128 cuts21134 = true := by
 decide +kernel
def pointBounds21134 : List (Nat × Nat × Nat) := [(2774073344,100734868109994,100735248895949)]
theorem point_links_checked21134 : (cuts21134.take 1).map (fun c => (2774007809-1+2*2^9*c.k,100734562794376+c.lower,100734943580154+c.upper)) = pointBounds21134 := by
 decide +kernel
def cuts21135 : List PrefixCut := [⟨21,99941542,99941601⟩,
⟨106,504468548,504468845⟩,
⟨128,610493727,610494084⟩]
theorem checked21135 : checkPrefixCuts (2^48) 2774138881 9 Manual.Count131072.C021135.packed 128 cuts21135 = true := by
 decide +kernel
def pointBounds21135 : List (Nat × Nat × Nat) := [(2774160384,100735273968743,100735654754930),(2774247424,100735678495749,100736059282174)]
theorem point_links_checked21135 : (cuts21135.take 2).map (fun c => (2774138881-1+2*2^9*c.k,100735174027201+c.lower,100735554813329+c.upper)) = pointBounds21135 := by
 decide +kernel
def cuts21136 : List PrefixCut := [⟨63,295546870,295547044⟩,
⟨128,610667687,610668043⟩]
theorem checked21136 : checkPrefixCuts (2^48) 2774269953 9 Manual.Count131072.C021136.packed 128 cuts21136 = true := by
 decide +kernel
def pointBounds21136 : List (Nat × Nat × Nat) := [(2774334464,100736080067798,100736460854457)]
theorem point_links_checked21136 : (cuts21136.take 1).map (fun c => (2774269953-1+2*2^9*c.k,100735784520928+c.lower,100736165307413+c.upper)) = pointBounds21136 := by
 decide +kernel
def cuts21137 : List PrefixCut := [⟨20,97192851,97192907⟩,
⟨105,502899298,502899592⟩,
⟨128,612465224,612465581⟩]
theorem checked21137 : checkPrefixCuts (2^48) 2774401025 9 Manual.Count131072.C021137.packed 128 cuts21137 = true := by
 decide +kernel
def pointBounds21137 : List (Nat × Nat × Nat) := [(2774421504,100736492381466,100736873168363),(2774508544,100736898087913,100737278875048)]
theorem point_links_checked21137 : (cuts21137.take 2).map (fun c => (2774401025-1+2*2^9*c.k,100736395188615+c.lower,100736775975456+c.upper)) = pointBounds21137 := by
 decide +kernel
def cuts21138 : List PrefixCut := [⟨62,292779948,292780112⟩,
⟨128,608581184,608581534⟩]
theorem checked21138 : checkPrefixCuts (2^48) 2774532097 9 Manual.Count131072.C021138.packed 128 cuts21138 = true := by
 decide +kernel
def pointBounds21138 : List (Nat × Nat × Nat) := [(2774595584,100737300433787,100737681221149)]
theorem point_links_checked21138 : (cuts21138.take 1).map (fun c => (2774532097-1+2*2^9*c.k,100737007653839+c.lower,100737388441037+c.upper)) = pointBounds21138 := by
 decide +kernel
def cuts21139 : List PrefixCut := [⟨19,92212920,92212973⟩,
⟨104,498185385,498185666⟩,
⟨128,612610122,612610469⟩]
theorem checked21139 : checkPrefixCuts (2^48) 2774663169 9 Manual.Count131072.C021139.packed 128 cuts21139 = true := by
 decide +kernel
def pointBounds21139 : List (Nat × Nat × Nat) := [(2774682624,100737708447943,100738089235544),(2774769664,100738114420408,100738495208237)]
theorem point_links_checked21139 : (cuts21139.take 2).map (fun c => (2774663169-1+2*2^9*c.k,100737616235023+c.lower,100737997022571+c.upper)) = pointBounds21139 := by
 decide +kernel
def cuts21140 : List PrefixCut := [⟨61,292042243,292042411⟩,
⟨128,611465362,611465712⟩]
theorem checked21140 : checkPrefixCuts (2^48) 2774794241 9 Manual.Count131072.C021140.packed 128 cuts21140 = true := by
 decide +kernel
def pointBounds21140 : List (Nat × Nat × Nat) := [(2774856704,100738520887388,100738901675451)]
theorem point_links_checked21140 : (cuts21140.take 1).map (fun c => (2774794241-1+2*2^9*c.k,100738228845145+c.lower,100738609633040+c.upper)) = pointBounds21140 := by
 decide +kernel
def cuts21141 : List PrefixCut := [⟨18,83886570,83886617⟩,
⟨103,495805431,495805710⟩,
⟨128,613870879,613871227⟩]
theorem checked21141 : checkPrefixCuts (2^48) 2774925313 9 Manual.Count131072.C021141.packed 128 cuts21141 = true := by
 decide +kernel
def pointBounds21141 : List (Nat × Nat × Nat) := [(2774943744,100738924197077,100739304985369),(2775030784,100739336115938,100739716904462)]
theorem point_links_checked21141 : (cuts21141.take 2).map (fun c => (2774925313-1+2*2^9*c.k,100738840310507+c.lower,100739221098752+c.upper)) = pointBounds21141 := by
 decide +kernel
def cuts21142 : List PrefixCut := [⟨60,282784674,282784841⟩,
⟨128,605626225,605626575⟩]
theorem checked21142 : checkPrefixCuts (2^48) 2775056385 9 Manual.Count131072.C021142.packed 128 cuts21142 = true := by
 decide +kernel
def pointBounds21142 : List (Nat × Nat × Nat) := [(2775117824,100739736966060,100740117754820)]
theorem point_links_checked21142 : (cuts21142.take 1).map (fun c => (2775056385-1+2*2^9*c.k,100739454181386+c.lower,100739834969979+c.upper)) = pointBounds21142 := by
 decide +kernel
def cuts21143 : List PrefixCut := [⟨17,82864408,82864455⟩,
⟨102,489774754,489775035⟩,
⟨128,613812923,613813276⟩]
theorem checked21143 : checkPrefixCuts (2^48) 2775187457 9 Manual.Count131072.C021143.packed 128 cuts21143 = true := by
 decide +kernel
def pointBounds21143 : List (Nat × Nat × Nat) := [(2775204864,100740142672019,100740523461009),(2775291904,100740549582365,100740930371589)]
theorem point_links_checked21143 : (cuts21143.take 2).map (fun c => (2775187457-1+2*2^9*c.k,100740059807611+c.lower,100740440596554+c.upper)) = pointBounds21143 := by
 decide +kernel
def cuts21144 : List PrefixCut := [⟨59,281946626,281946785⟩,
⟨128,614696603,614696953⟩]
theorem checked21144 : checkPrefixCuts (2^48) 2775318529 9 Manual.Count131072.C021144.packed 128 cuts21144 = true := by
 decide +kernel
def pointBounds21144 : List (Nat × Nat × Nat) := [(2775378944,100740955567160,100741336356615)]
theorem point_links_checked21144 : (cuts21144.take 1).map (fun c => (2775318529-1+2*2^9*c.k,100740673620534+c.lower,100741054409830+c.upper)) = pointBounds21144 := by
 decide +kernel
def cuts21145 : List PrefixCut := [⟨16,74033438,74033480⟩,
⟨101,484556382,484556662⟩,
⟨128,609495564,609495916⟩]
theorem checked21145 : checkPrefixCuts (2^48) 2775449601 9 Manual.Count131072.C021145.packed 128 cuts21145 = true := by
 decide +kernel
def pointBounds21145 : List (Nat × Nat × Nat) := [(2775465984,100741362350575,100741743140263),(2775553024,100741772873519,100742153663445)]
theorem point_links_checked21145 : (cuts21145.take 2).map (fun c => (2775449601-1+2*2^9*c.k,100741288317137+c.lower,100741669106783+c.upper)) = pointBounds21145 := by
 decide +kernel
def cuts21146 : List PrefixCut := [⟨58,275936848,275937013⟩,
⟨128,608249817,608250176⟩]
theorem checked21146 : checkPrefixCuts (2^48) 2775580673 9 Manual.Count131072.C021146.packed 128 cuts21146 = true := by
 decide +kernel
def pointBounds21146 : List (Nat × Nat × Nat) := [(2775640064,100742173749549,100742554539712)]
theorem point_links_checked21146 : (cuts21146.take 1).map (fun c => (2775580673-1+2*2^9*c.k,100741897812701+c.lower,100742278602699+c.upper)) = pointBounds21146 := by
 decide +kernel
def cuts21147 : List PrefixCut := [⟨15,71187082,71187124⟩,
⟨100,477716721,477717001⟩,
⟨128,609032465,609032821⟩]
theorem checked21147 : checkPrefixCuts (2^48) 2775711745 9 Manual.Count131072.C021147.packed 128 cuts21147 = true := by
 decide +kernel
def pointBounds21147 : List (Nat × Nat × Nat) := [(2775727104,100742577249600,100742958039999),(2775814144,100742983779239,100743364569876)]
theorem point_links_checked21147 : (cuts21147.take 2).map (fun c => (2775711745-1+2*2^9*c.k,100742506062518+c.lower,100742886852875+c.upper)) = pointBounds21147 := by
 decide +kernel
def cuts21148 : List PrefixCut := [⟨57,271854805,271854964⟩,
⟨128,611234399,611234760⟩]
theorem checked21148 : checkPrefixCuts (2^48) 2775842817 9 Manual.Count131072.C021148.packed 128 cuts21148 = true := by
 decide +kernel
def pointBounds21148 : List (Nat × Nat × Nat) := [(2775901184,100743386949788,100743767740660)]
theorem point_links_checked21148 : (cuts21148.take 1).map (fun c => (2775842817-1+2*2^9*c.k,100743115094983+c.lower,100743495885696+c.upper)) = pointBounds21148 := by
 decide +kernel
def cuts21149 : List PrefixCut := [⟨14,64184014,64184051⟩,
⟨99,469864214,469864478⟩,
⟨128,607758102,607758446⟩]
theorem checked21149 : checkPrefixCuts (2^48) 2775973889 9 Manual.Count131072.C021149.packed 128 cuts21149 = true := by
 decide +kernel
def pointBounds21149 : List (Nat × Nat × Nat) := [(2775988224,100743790513396,100744171304507),(2776075264,100744196193596,100744576984934)]
theorem point_links_checked21149 : (cuts21149.take 2).map (fun c => (2775973889-1+2*2^9*c.k,100743726329382+c.lower,100744107120456+c.upper)) = pointBounds21149 := by
 decide +kernel
def cuts21150 : List PrefixCut := [⟨56,273147268,273147422⟩,
⟨128,615130970,615131321⟩]
theorem checked21150 : checkPrefixCuts (2^48) 2776104961 9 Manual.Count131072.C021150.packed 128 cuts21150 = true := by
 decide +kernel
def pointBounds21150 : List (Nat × Nat × Nat) := [(2776162304,100744607234752,100744988026324)]
theorem point_links_checked21150 : (cuts21150.take 1).map (fun c => (2776104961-1+2*2^9*c.k,100744334087484+c.lower,100744714878902+c.upper)) = pointBounds21150 := by
 decide +kernel
def cuts21151 : List PrefixCut := [⟨13,59311386,59311423⟩,
⟨98,462114677,462114944⟩,
⟨128,609018657,609019008⟩]
theorem checked21151 : checkPrefixCuts (2^48) 2776236033 9 Manual.Count131072.C021151.packed 128 cuts21151 = true := by
 decide +kernel
def pointBounds21151 : List (Nat × Nat × Nat) := [(2776249344,100745008529840,100745389321646),(2776336384,100745411333131,100745792125167)]
theorem point_links_checked21151 : (cuts21151.take 2).map (fun c => (2776236033-1+2*2^9*c.k,100744949218454+c.lower,100745330010223+c.upper)) = pointBounds21151 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000035
