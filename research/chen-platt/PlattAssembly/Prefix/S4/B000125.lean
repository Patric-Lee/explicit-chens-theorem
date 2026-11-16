import PlattAssemblyKernel
import PlattCertificates.Count131072.C034000
import PlattCertificates.Count131072.C034001
import PlattCertificates.Count131072.C034002
import PlattCertificates.Count131072.C034003
import PlattCertificates.Count131072.C034004
import PlattCertificates.Count131072.C034005
import PlattCertificates.Count131072.C034006
import PlattCertificates.Count131072.C034007
import PlattCertificates.Count131072.C034008
import PlattCertificates.Count131072.C034009
import PlattCertificates.Count131072.C034010
import PlattCertificates.Count131072.C034011
import PlattCertificates.Count131072.C034012
import PlattCertificates.Count131072.C034013
import PlattCertificates.Count131072.C034014
import PlattCertificates.Count131072.C034015
import PlattCertificates.Count131072.C034016
import PlattCertificates.Count131072.C034017
import PlattCertificates.Count131072.C034018
import PlattCertificates.Count131072.C034019
import PlattCertificates.Count131072.C034020
import PlattCertificates.Count131072.C034021
import PlattCertificates.Count131072.C034022
import PlattCertificates.Count131072.C034023
import PlattCertificates.Count131072.C034024
import PlattCertificates.Count131072.C034025
import PlattCertificates.Count131072.C034026
import PlattCertificates.Count131072.C034027
import PlattCertificates.Count131072.C034028
import PlattCertificates.Count131072.C034029
import PlattCertificates.Count131072.C034030
import PlattCertificates.Count131072.C034031
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000125
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts34000 : List PrefixCut := [⟨57,328334037,328334244⟩,
⟨64,370487393,370487626⟩]
theorem checked34000 : checkPrefixCuts (2^48) 4460380161 10 Manual.Count131072.C034000.packed 64 cuts34000 = true := by
 decide +kernel
def pointBounds34000 : List (Nat × Nat × Nat) := [(4460496896,106816878257276,106817262510098)]
theorem point_links_checked34000 : (cuts34000.take 1).map (fun c => (4460380161-1+2*2^10*c.k,106816549923239+c.lower,106816934175854+c.upper)) = pointBounds34000 := by
 decide +kernel
def cuts34001 : List PrefixCut := [⟨62,363282965,363283197⟩,
⟨64,375083021,375083260⟩]
theorem checked34001 : checkPrefixCuts (2^48) 4460511233 10 Manual.Count131072.C034001.packed 64 cuts34001 = true := by
 decide +kernel
def pointBounds34001 : List (Nat × Nat × Nat) := [(4460638208,106817283693597,106817667946677)]
theorem point_links_checked34001 : (cuts34001.take 1).map (fun c => (4460511233-1+2*2^10*c.k,106816920410632+c.lower,106817304663480+c.upper)) = pointBounds34001 := by
 decide +kernel
def cuts34002 : List PrefixCut := [⟨64,366742709,366742942⟩]
theorem checked34002 : checkPrefixCuts (2^48) 4460642305 10 Manual.Count131072.C034002.packed 64 cuts34002 = true := by
 decide +kernel
def cuts34003 : List PrefixCut := [⟨3,17794194,17794205⟩,
⟨64,368814161,368814395⟩]
theorem checked34003 : checkPrefixCuts (2^48) 4460773377 10 Manual.Count131072.C034003.packed 64 cuts34003 = true := by
 decide +kernel
def pointBounds34003 : List (Nat × Nat × Nat) := [(4460779520,106817680030556,106818064283887)]
theorem point_links_checked34003 : (cuts34003.take 1).map (fun c => (4460773377-1+2*2^10*c.k,106817662236362+c.lower,106818046489682+c.upper)) = pointBounds34003 := by
 decide +kernel
def cuts34004 : List PrefixCut := [⟨8,45052007,45052039⟩,
⟨64,373598692,373598928⟩]
theorem checked34004 : checkPrefixCuts (2^48) 4460904449 10 Manual.Count131072.C034004.packed 64 cuts34004 = true := by
 decide +kernel
def pointBounds34004 : List (Nat × Nat × Nat) := [(4460920832,106818076102530,106818460356116)]
theorem point_links_checked34004 : (cuts34004.take 1).map (fun c => (4460904449-1+2*2^10*c.k,106818031050523+c.lower,106818415304077+c.upper)) = pointBounds34004 := by
 decide +kernel
def cuts34005 : List PrefixCut := [⟨13,74832004,74832050⟩,
⟨64,369297304,369297543⟩]
theorem checked34005 : checkPrefixCuts (2^48) 4461035521 10 Manual.Count131072.C034005.packed 64 cuts34005 = true := by
 decide +kernel
def pointBounds34005 : List (Nat × Nat × Nat) := [(4461062144,106818479481219,106818863735055)]
theorem point_links_checked34005 : (cuts34005.take 1).map (fun c => (4461035521-1+2*2^10*c.k,106818404649215+c.lower,106818788903005+c.upper)) = pointBounds34005 := by
 decide +kernel
def cuts34006 : List PrefixCut := [⟨18,105493495,105493561⟩,
⟨64,371936403,371936634⟩]
theorem checked34006 : checkPrefixCuts (2^48) 4461166593 10 Manual.Count131072.C034006.packed 64 cuts34006 = true := by
 decide +kernel
def pointBounds34006 : List (Nat × Nat × Nat) := [(4461203456,106818879440014,106819263694109)]
theorem point_links_checked34006 : (cuts34006.take 1).map (fun c => (4461166593-1+2*2^10*c.k,106818773946519+c.lower,106819158200548+c.upper)) = pointBounds34006 := by
 decide +kernel
def cuts34007 : List PrefixCut := [⟨23,131799751,131799830⟩,
⟨64,370852865,370853097⟩]
theorem checked34007 : checkPrefixCuts (2^48) 4461297665 10 Manual.Count131072.C034007.packed 64 cuts34007 = true := by
 decide +kernel
def pointBounds34007 : List (Nat × Nat × Nat) := [(4461344768,106819277682673,106819661937012)]
theorem point_links_checked34007 : (cuts34007.take 1).map (fun c => (4461297665-1+2*2^10*c.k,106819145882922+c.lower,106819530137182+c.upper)) = pointBounds34007 := by
 decide +kernel
def cuts34008 : List PrefixCut := [⟨28,163971807,163971908⟩,
⟨64,374690495,374690730⟩]
theorem checked34008 : checkPrefixCuts (2^48) 4461428737 10 Manual.Count131072.C034008.packed 64 cuts34008 = true := by
 decide +kernel
def pointBounds34008 : List (Nat × Nat × Nat) := [(4461486080,106819680707594,106820064962187)]
theorem point_links_checked34008 : (cuts34008.take 1).map (fun c => (4461428737-1+2*2^10*c.k,106819516735787+c.lower,106819900990279+c.upper)) = pointBounds34008 := by
 decide +kernel
def cuts34009 : List PrefixCut := [⟨33,191347182,191347301⟩,
⟨64,370515660,370515891⟩]
theorem checked34009 : checkPrefixCuts (2^48) 4461559809 10 Manual.Count131072.C034009.packed 64 cuts34009 = true := by
 decide +kernel
def pointBounds34009 : List (Nat × Nat × Nat) := [(4461627392,106820082773464,106820467028310)]
theorem point_links_checked34009 : (cuts34009.take 1).map (fun c => (4461559809-1+2*2^10*c.k,106819891426282+c.lower,106820275681009+c.upper)) = pointBounds34009 := by
 decide +kernel
def cuts34010 : List PrefixCut := [⟨38,223263097,223263236⟩,
⟨64,375236234,375236469⟩]
theorem checked34010 : checkPrefixCuts (2^48) 4461690881 10 Manual.Count131072.C034010.packed 64 cuts34010 = true := by
 decide +kernel
def pointBounds34010 : List (Nat × Nat × Nat) := [(4461768704,106820485205039,106820869460136)]
theorem point_links_checked34010 : (cuts34010.take 1).map (fun c => (4461690881-1+2*2^10*c.k,106820261941942+c.lower,106820646196900+c.upper)) = pointBounds34010 := by
 decide +kernel
def cuts34011 : List PrefixCut := [⟨43,248300849,248301008⟩,
⟨64,369736860,369737097⟩]
theorem checked34011 : checkPrefixCuts (2^48) 4461821953 10 Manual.Count131072.C034011.packed 64 cuts34011 = true := by
 decide +kernel
def pointBounds34011 : List (Nat × Nat × Nat) := [(4461910016,106820885479025,106821269734377)]
theorem point_links_checked34011 : (cuts34011.take 1).map (fun c => (4461821953-1+2*2^10*c.k,106820637178176+c.lower,106821021433369+c.upper)) = pointBounds34011 := by
 decide +kernel
def cuts34012 : List PrefixCut := [⟨48,280339257,280339436⟩,
⟨64,373384789,373385027⟩]
theorem checked34012 : checkPrefixCuts (2^48) 4461953025 10 Manual.Count131072.C034012.packed 64 cuts34012 = true := by
 decide +kernel
def pointBounds34012 : List (Nat × Nat × Nat) := [(4462051328,106821287254293,106821671509902)]
theorem point_links_checked34012 : (cuts34012.take 1).map (fun c => (4461953025-1+2*2^10*c.k,106821006915036+c.lower,106821391170466+c.upper)) = pointBounds34012 := by
 decide +kernel
def cuts34013 : List PrefixCut := [⟨53,302219717,302219908⟩,
⟨64,366561102,366561333⟩]
theorem checked34013 : checkPrefixCuts (2^48) 4462084097 10 Manual.Count131072.C034013.packed 64 cuts34013 = true := by
 decide +kernel
def pointBounds34013 : List (Nat × Nat × Nat) := [(4462192640,106821682519542,106822066775401)]
theorem point_links_checked34013 : (cuts34013.take 1).map (fun c => (4462084097-1+2*2^10*c.k,106821380299825+c.lower,106821764555493+c.upper)) = pointBounds34013 := by
 decide +kernel
def cuts34014 : List PrefixCut := [⟨58,336903869,336904083⟩,
⟨64,373173643,373173879⟩]
theorem checked34014 : checkPrefixCuts (2^48) 4462215169 10 Manual.Count131072.C034014.packed 64 cuts34014 = true := by
 decide +kernel
def pointBounds34014 : List (Nat × Nat × Nat) := [(4462333952,106822083764796,106822468020909)]
theorem point_links_checked34014 : (cuts34014.take 1).map (fun c => (4462215169-1+2*2^10*c.k,106821746860927+c.lower,106822131116826+c.upper)) = pointBounds34014 := by
 decide +kernel
def cuts34015 : List PrefixCut := [⟨63,360736576,360736806⟩,
⟨64,366854942,366855176⟩]
theorem checked34015 : checkPrefixCuts (2^48) 4462346241 10 Manual.Count131072.C034015.packed 64 cuts34015 = true := by
 decide +kernel
def pointBounds34015 : List (Nat × Nat × Nat) := [(4462475264,106822480771146,106822865027511)]
theorem point_links_checked34015 : (cuts34015.take 1).map (fun c => (4462346241-1+2*2^10*c.k,106822120034570+c.lower,106822504290705+c.upper)) = pointBounds34015 := by
 decide +kernel
def cuts34016 : List PrefixCut := [⟨64,371890218,371890454⟩]
theorem checked34016 : checkPrefixCuts (2^48) 4462477313 10 Manual.Count131072.C034016.packed 64 cuts34016 = true := by
 decide +kernel
def cuts34017 : List PrefixCut := [⟨4,23968127,23968142⟩,
⟨64,371500850,371501081⟩]
theorem checked34017 : checkPrefixCuts (2^48) 4462608385 10 Manual.Count131072.C034017.packed 64 cuts34017 = true := by
 decide +kernel
def pointBounds34017 : List (Nat × Nat × Nat) := [(4462616576,106822882747857,106823267004477)]
theorem point_links_checked34017 : (cuts34017.take 1).map (fun c => (4462608385-1+2*2^10*c.k,106822858779730+c.lower,106823243036335+c.upper)) = pointBounds34017 := by
 decide +kernel
def cuts34018 : List PrefixCut := [⟨9,52475980,52476016⟩,
⟨64,370102352,370102590⟩]
theorem checked34018 : checkPrefixCuts (2^48) 4462739457 10 Manual.Count131072.C034018.packed 64 cuts34018 = true := by
 decide +kernel
def pointBounds34018 : List (Nat × Nat × Nat) := [(4462757888,106823282756560,106823667013432)]
theorem point_links_checked34018 : (cuts34018.take 1).map (fun c => (4462739457-1+2*2^10*c.k,106823230280580+c.lower,106823614537416+c.upper)) = pointBounds34018 := by
 decide +kernel
def cuts34019 : List PrefixCut := [⟨14,76945601,76945651⟩,
⟨64,368262414,368262649⟩]
theorem checked34019 : checkPrefixCuts (2^48) 4462870529 10 Manual.Count131072.C034019.packed 64 cuts34019 = true := by
 decide +kernel
def pointBounds34019 : List (Nat × Nat × Nat) := [(4462899200,106823677328533,106824061585657)]
theorem point_links_checked34019 : (cuts34019.take 1).map (fun c => (4462870529-1+2*2^10*c.k,106823600382932+c.lower,106823984640006+c.upper)) = pointBounds34019 := by
 decide +kernel
def cuts34020 : List PrefixCut := [⟨19,109423395,109423466⟩,
⟨64,374369169,374369408⟩]
theorem checked34020 : checkPrefixCuts (2^48) 4463001601 10 Manual.Count131072.C034020.packed 64 cuts34020 = true := by
 decide +kernel
def pointBounds34020 : List (Nat × Nat × Nat) := [(4463040512,106824078068741,106824462326121)]
theorem point_links_checked34020 : (cuts34020.take 1).map (fun c => (4463001601-1+2*2^10*c.k,106823968645346+c.lower,106824352902655+c.upper)) = pointBounds34020 := by
 decide +kernel
def cuts34021 : List PrefixCut := [⟨24,137169239,137169324⟩,
⟨64,370258903,370259138⟩]
theorem checked34021 : checkPrefixCuts (2^48) 4463132673 10 Manual.Count131072.C034021.packed 64 cuts34021 = true := by
 decide +kernel
def pointBounds34021 : List (Nat × Nat × Nat) := [(4463181824,106824480183754,106824864441387)]
theorem point_links_checked34021 : (cuts34021.take 1).map (fun c => (4463132673-1+2*2^10*c.k,106824343014515+c.lower,106824727272063+c.upper)) = pointBounds34021 := by
 decide +kernel
def cuts34022 : List PrefixCut := [⟨29,168949501,168949606⟩,
⟨64,371383254,371383490⟩]
theorem checked34022 : checkPrefixCuts (2^48) 4463263745 10 Manual.Count131072.C034022.packed 64 cuts34022 = true := by
 decide +kernel
def pointBounds34022 : List (Nat × Nat × Nat) := [(4463323136,106824882222919,106825266480807)]
theorem point_links_checked34022 : (cuts34022.take 1).map (fun c => (4463263745-1+2*2^10*c.k,106824713273418+c.lower,106825097531201+c.upper)) = pointBounds34022 := by
 decide +kernel
def cuts34023 : List PrefixCut := [⟨34,197763886,197764012⟩,
⟨64,372129040,372129278⟩]
theorem checked34023 : checkPrefixCuts (2^48) 4463394817 10 Manual.Count131072.C034023.packed 64 cuts34023 = true := by
 decide +kernel
def pointBounds34023 : List (Nat × Nat × Nat) := [(4463464448,106825282420558,106825666678703)]
theorem point_links_checked34023 : (cuts34023.take 1).map (fun c => (4463394817-1+2*2^10*c.k,106825084656672+c.lower,106825468914691+c.upper)) = pointBounds34023 := by
 decide +kernel
def cuts34024 : List PrefixCut := [⟨39,228972820,228972967⟩,
⟨64,376090909,376091145⟩]
theorem checked34024 : checkPrefixCuts (2^48) 4463525889 10 Manual.Count131072.C034024.packed 64 cuts34024 = true := by
 decide +kernel
def pointBounds34024 : List (Nat × Nat × Nat) := [(4463605760,106825685758532,106826070016936)]
theorem point_links_checked34024 : (cuts34024.take 1).map (fun c => (4463525889-1+2*2^10*c.k,106825456785712+c.lower,106825841043969+c.upper)) = pointBounds34024 := by
 decide +kernel
def cuts34025 : List PrefixCut := [⟨44,259927642,259927805⟩,
⟨64,376269082,376269320⟩]
theorem checked34025 : checkPrefixCuts (2^48) 4463656961 10 Manual.Count131072.C034025.packed 64 cuts34025 = true := by
 decide +kernel
def pointBounds34025 : List (Nat × Nat × Nat) := [(4463747072,106826092804263,106826477062919)]
theorem point_links_checked34025 : (cuts34025.take 1).map (fun c => (4463656961-1+2*2^10*c.k,106825832876621+c.lower,106826217135114+c.upper)) = pointBounds34025 := by
 decide +kernel
def cuts34026 : List PrefixCut := [⟨49,285646834,285647016⟩,
⟨64,374240194,374240434⟩]
theorem checked34026 : checkPrefixCuts (2^48) 4463788033 10 Manual.Count131072.C034026.packed 64 cuts34026 = true := by
 decide +kernel
def pointBounds34026 : List (Nat × Nat × Nat) := [(4463888384,106826494792537,106826879051450)]
theorem point_links_checked34026 : (cuts34026.take 1).map (fun c => (4463788033-1+2*2^10*c.k,106826209145703+c.lower,106826593404434+c.upper)) = pointBounds34026 := by
 decide +kernel
def cuts34027 : List PrefixCut := [⟨54,307833408,307833605⟩,
⟨64,366032109,366032343⟩]
theorem checked34027 : checkPrefixCuts (2^48) 4463919105 10 Manual.Count131072.C034027.packed 64 cuts34027 = true := by
 decide +kernel
def pointBounds34027 : List (Nat × Nat × Nat) := [(4464029696,106826891219305,106827275478473)]
theorem point_links_checked34027 : (cuts34027.take 1).map (fun c => (4463919105-1+2*2^10*c.k,106826583385897+c.lower,106826967644868+c.upper)) = pointBounds34027 := by
 decide +kernel
def cuts34028 : List PrefixCut := [⟨59,341935588,341935807⟩,
⟨64,369867592,369867827⟩]
theorem checked34028 : checkPrefixCuts (2^48) 4464050177 10 Manual.Count131072.C034028.packed 64 cuts34028 = true := by
 decide +kernel
def pointBounds34028 : List (Nat × Nat × Nat) := [(4464171008,106827291353594,106827675613018)]
theorem point_links_checked34028 : (cuts34028.take 1).map (fun c => (4464050177-1+2*2^10*c.k,106826949418006+c.lower,106827333677211+c.upper)) = pointBounds34028 := by
 decide +kernel
def cuts34029 : List PrefixCut := [⟨64,378873052,378873294⟩]
theorem checked34029 : checkPrefixCuts (2^48) 4464181249 10 Manual.Count131072.C034029.packed 64 cuts34029 = true := by
 decide +kernel
def pointBounds34029 : List (Nat × Nat × Nat) := [(4464312320,106827698158650,106828082418332)]
theorem point_links_checked34029 : (cuts34029.take 1).map (fun c => (4464181249-1+2*2^10*c.k,106827319285598+c.lower,106827703545038+c.upper)) = pointBounds34029 := by
 decide +kernel
def cuts34030 : List PrefixCut := [⟨64,374700604,374700843⟩]
theorem checked34030 : checkPrefixCuts (2^48) 4464312321 10 Manual.Count131072.C034030.packed 64 cuts34030 = true := by
 decide +kernel
def cuts34031 : List PrefixCut := [⟨5,28686875,28686893⟩,
⟨64,370591583,370591814⟩]
theorem checked34031 : checkPrefixCuts (2^48) 4464443393 10 Manual.Count131072.C034031.packed 64 cuts34031 = true := by
 decide +kernel
def pointBounds34031 : List (Nat × Nat × Nat) := [(4464453632,106828101546129,106828485806068)]
theorem point_links_checked34031 : (cuts34031.take 1).map (fun c => (4464443393-1+2*2^10*c.k,106828072859254+c.lower,106828457119175+c.upper)) = pointBounds34031 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000125
