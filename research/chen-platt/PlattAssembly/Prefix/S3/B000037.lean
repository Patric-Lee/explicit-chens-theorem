import PlattAssemblyKernel
import PlattCertificates.Count131072.C021184
import PlattCertificates.Count131072.C021185
import PlattCertificates.Count131072.C021186
import PlattCertificates.Count131072.C021187
import PlattCertificates.Count131072.C021188
import PlattCertificates.Count131072.C021189
import PlattCertificates.Count131072.C021190
import PlattCertificates.Count131072.C021191
import PlattCertificates.Count131072.C021192
import PlattCertificates.Count131072.C021193
import PlattCertificates.Count131072.C021194
import PlattCertificates.Count131072.C021195
import PlattCertificates.Count131072.C021196
import PlattCertificates.Count131072.C021197
import PlattCertificates.Count131072.C021198
import PlattCertificates.Count131072.C021199
import PlattCertificates.Count131072.C021200
import PlattCertificates.Count131072.C021201
import PlattCertificates.Count131072.C021202
import PlattCertificates.Count131072.C021203
import PlattCertificates.Count131072.C021204
import PlattCertificates.Count131072.C021205
import PlattCertificates.Count131072.C021206
import PlattCertificates.Count131072.C021207
import PlattCertificates.Count131072.C021208
import PlattCertificates.Count131072.C021209
import PlattCertificates.Count131072.C021210
import PlattCertificates.Count131072.C021211
import PlattCertificates.Count131072.C021212
import PlattCertificates.Count131072.C021213
import PlattCertificates.Count131072.C021214
import PlattCertificates.Count131072.C021215
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000037
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts21184 : List PrefixCut := [⟨39,187880630,187880729⟩,
⟨124,592482894,592483222⟩,
⟨128,610703362,610703701⟩]
theorem checked21184 : checkPrefixCuts (2^48) 2780561409 9 Manual.Count131072.C021184.packed 128 cuts21184 = true := by
 decide +kernel
def pointBounds21184 : List (Nat × Nat × Nat) := [(2780601344,100765302937282,100765683740780),(2780688384,100765707539546,100766088343273)]
theorem point_links_checked21184 : (cuts21184.take 2).map (fun c => (2780561409-1+2*2^9*c.k,100765115056652+c.lower,100765495860051+c.upper)) = pointBounds21184 := by
 decide +kernel
def cuts21185 : List PrefixCut := [⟨81,381611665,381611889⟩,
⟨128,601463353,601463708⟩]
theorem checked21185 : checkPrefixCuts (2^48) 2780692481 9 Manual.Count131072.C021185.packed 128 cuts21185 = true := by
 decide +kernel
def pointBounds21185 : List (Nat × Nat × Nat) := [(2780775424,100766107371679,100766488175641)]
theorem point_links_checked21185 : (cuts21185.take 1).map (fun c => (2780692481-1+2*2^9*c.k,100765725760014+c.lower,100766106563752+c.upper)) = pointBounds21185 := by
 decide +kernel
def cuts21186 : List PrefixCut := [⟨38,183206865,183206970⟩,
⟨123,585746701,585747042⟩,
⟨128,610240802,610241158⟩]
theorem checked21186 : checkPrefixCuts (2^48) 2780823553 9 Manual.Count131072.C021186.packed 128 cuts21186 = true := by
 decide +kernel
def pointBounds21186 : List (Nat × Nat × Nat) := [(2780862464,100766510430232,100766891234430),(2780949504,100766912970068,100767293774502)]
theorem point_links_checked21186 : (cuts21186.take 2).map (fun c => (2780823553-1+2*2^9*c.k,100766327223367+c.lower,100766708027460+c.upper)) = pointBounds21186 := by
 decide +kernel
def cuts21187 : List PrefixCut := [⟨80,383701209,383701434⟩,
⟨128,609301235,609301588⟩]
theorem checked21187 : checkPrefixCuts (2^48) 2780954625 9 Manual.Count131072.C021187.packed 128 cuts21187 = true := by
 decide +kernel
def pointBounds21187 : List (Nat × Nat × Nat) := [(2781036544,100767321165378,100767701970052)]
theorem point_links_checked21187 : (cuts21187.take 1).map (fun c => (2780954625-1+2*2^9*c.k,100766937464169+c.lower,100767318268618+c.upper)) = pointBounds21187 := by
 decide +kernel
def cuts21188 : List PrefixCut := [⟨37,170234771,170234876⟩,
⟨122,575773138,575773469⟩,
⟨128,603199904,603200250⟩]
theorem checked21188 : checkPrefixCuts (2^48) 2781085697 9 Manual.Count131072.C021188.packed 128 cuts21188 = true := by
 decide +kernel
def pointBounds21188 : List (Nat × Nat × Nat) := [(2781123584,100767717000175,100768097805082),(2781210624,100768122538542,100768503343675)]
theorem point_links_checked21188 : (cuts21188.take 2).map (fun c => (2781085697-1+2*2^9*c.k,100767546765404+c.lower,100767927570206+c.upper)) = pointBounds21188 := by
 decide +kernel
def cuts21189 : List PrefixCut := [⟨79,380628977,380629196⟩,
⟨128,616429202,616429552⟩]
theorem checked21189 : checkPrefixCuts (2^48) 2781216769 9 Manual.Count131072.C021189.packed 128 cuts21189 = true := by
 decide +kernel
def pointBounds21189 : List (Nat × Nat × Nat) := [(2781297664,100768530594285,100768911399652)]
theorem point_links_checked21189 : (cuts21189.take 1).map (fun c => (2781216769-1+2*2^9*c.k,100768149965308+c.lower,100768530770456+c.upper)) = pointBounds21189 := by
 decide +kernel
def cuts21190 : List PrefixCut := [⟨36,177505197,177505298⟩,
⟨121,582499487,582499820⟩,
⟨128,614275112,614275465⟩]
theorem checked21190 : checkPrefixCuts (2^48) 2781347841 9 Manual.Count131072.C021190.packed 128 cuts21190 = true := by
 decide +kernel
def pointBounds21190 : List (Nat × Nat × Nat) := [(2781384704,100768943899707,100769324705306),(2781471744,100769348893997,100769729699828)]
theorem point_links_checked21190 : (cuts21190.take 2).map (fun c => (2781347841-1+2*2^9*c.k,100768766394510+c.lower,100769147200008+c.upper)) = pointBounds21190 := by
 decide +kernel
def cuts21191 : List PrefixCut := [⟨78,373104793,373105008⟩,
⟨128,608376843,608377196⟩]
theorem checked21191 : checkPrefixCuts (2^48) 2781478913 9 Manual.Count131072.C021191.packed 128 cuts21191 = true := by
 decide +kernel
def pointBounds21191 : List (Nat × Nat × Nat) := [(2781558784,100769753774415,100770134580481)]
theorem point_links_checked21191 : (cuts21191.take 1).map (fun c => (2781478913-1+2*2^9*c.k,100769380669622+c.lower,100769761475473+c.upper)) = pointBounds21191 := by
 decide +kernel
def cuts21192 : List PrefixCut := [⟨35,169899207,169899307⟩,
⟨120,577486375,577486710⟩,
⟨128,617657510,617657868⟩]
theorem checked21192 : checkPrefixCuts (2^48) 2781609985 9 Manual.Count131072.C021192.packed 128 cuts21192 = true := by
 decide +kernel
def pointBounds21192 : List (Nat × Nat × Nat) := [(2781645824,100770158945672,100770539751976),(2781732864,100770566532840,100770947339379)]
theorem point_links_checked21192 : (cuts21192.take 2).map (fun c => (2781609985-1+2*2^9*c.k,100769989046465+c.lower,100770369852669+c.upper)) = pointBounds21192 := by
 decide +kernel
def cuts21193 : List PrefixCut := [⟨77,370540069,370540279⟩,
⟨128,614795290,614795639⟩]
theorem checked21193 : checkPrefixCuts (2^48) 2781741057 9 Manual.Count131072.C021193.packed 128 cuts21193 = true := by
 decide +kernel
def pointBounds21193 : List (Nat × Nat × Nat) := [(2781819904,100770977244044,100771358050816)]
theorem point_links_checked21193 : (cuts21193.take 1).map (fun c => (2781741057-1+2*2^9*c.k,100770606703975+c.lower,100770987510537+c.upper)) = pointBounds21193 := by
 decide +kernel
def cuts21194 : List PrefixCut := [⟨34,159967441,159967533⟩,
⟨119,562255034,562255357⟩,
⟨128,602928278,602928625⟩]
theorem checked21194 : checkPrefixCuts (2^48) 2781872129 9 Manual.Count131072.C021194.packed 128 cuts21194 = true := by
 decide +kernel
def pointBounds21194 : List (Nat × Nat × Nat) := [(2781906944,100771381466706,100771762273709),(2781993984,100771783754299,100772164561533)]
theorem point_links_checked21194 : (cuts21194.take 2).map (fun c => (2781872129-1+2*2^9*c.k,100771221499265+c.lower,100771602306176+c.upper)) = pointBounds21194 := by
 decide +kernel
def cuts21195 : List PrefixCut := [⟨76,362107630,362107836⟩,
⟨128,608970370,608970716⟩]
theorem checked21195 : checkPrefixCuts (2^48) 2782003201 9 Manual.Count131072.C021195.packed 128 cuts21195 = true := by
 decide +kernel
def pointBounds21195 : List (Nat × Nat × Nat) := [(2782081024,100772186535173,100772567342637)]
theorem point_links_checked21195 : (cuts21195.take 1).map (fun c => (2782003201-1+2*2^9*c.k,100771824427543+c.lower,100772205234801+c.upper)) = pointBounds21195 := by
 decide +kernel
def cuts21196 : List PrefixCut := [⟨33,158637187,158637277⟩,
⟨118,559470608,559470935⟩,
⟨128,604287902,604288257⟩]
theorem checked21196 : checkPrefixCuts (2^48) 2782134273 9 Manual.Count131072.C021196.packed 128 cuts21196 = true := by
 decide +kernel
def pointBounds21196 : List (Nat × Nat × Nat) := [(2782168064,100772592035100,100772972842794),(2782255104,100772992868521,100773373676452)]
theorem point_links_checked21196 : (cuts21196.take 2).map (fun c => (2782134273-1+2*2^9*c.k,100772433397913+c.lower,100772814205517+c.upper)) = pointBounds21196 := by
 decide +kernel
def cuts21197 : List PrefixCut := [⟨75,360657243,360657446⟩,
⟨128,616298039,616298388⟩]
theorem checked21197 : checkPrefixCuts (2^48) 2782265345 9 Manual.Count131072.C021197.packed 128 cuts21197 = true := by
 decide +kernel
def pointBounds21197 : List (Nat × Nat × Nat) := [(2782342144,100773398343058,100773779151220)]
theorem point_links_checked21197 : (cuts21197.take 1).map (fun c => (2782265345-1+2*2^9*c.k,100773037685815+c.lower,100773418493774+c.upper)) = pointBounds21197 := by
 decide +kernel
def cuts21198 : List PrefixCut := [⟨32,146786313,146786399⟩,
⟨117,552640174,552640497⟩,
⟨128,606658649,606659005⟩]
theorem checked21198 : checkPrefixCuts (2^48) 2782396417 9 Manual.Count131072.C021198.packed 128 cuts21198 = true := by
 decide +kernel
def pointBounds21198 : List (Nat × Nat × Nat) := [(2782429184,100773800770167,100774181578561),(2782516224,100774206624028,100774587432659)]
theorem point_links_checked21198 : (cuts21198.take 2).map (fun c => (2782396417-1+2*2^9*c.k,100773653983854+c.lower,100774034792162+c.upper)) = pointBounds21198 := by
 decide +kernel
def cuts21199 : List PrefixCut := [⟨74,349293810,349294013⟩,
⟨128,609867123,609867474⟩]
theorem checked21199 : checkPrefixCuts (2^48) 2782527489 9 Manual.Count131072.C021199.packed 128 cuts21199 = true := by
 decide +kernel
def pointBounds21199 : List (Nat × Nat × Nat) := [(2782603264,100774609936313,100774990745180)]
theorem point_links_checked21199 : (cuts21199.take 1).map (fun c => (2782527489-1+2*2^9*c.k,100774260642503+c.lower,100774641451167+c.upper)) = pointBounds21199 := by
 decide +kernel
def cuts21200 : List PrefixCut := [⟨31,143232159,143232244⟩,
⟨116,550666378,550666698⟩,
⟨128,608523430,608523780⟩]
theorem checked21200 : checkPrefixCuts (2^48) 2782658561 9 Manual.Count131072.C021200.packed 128 cuts21200 = true := by
 decide +kernel
def pointBounds21200 : List (Nat × Nat × Nat) := [(2782690304,100775013741785,100775394550885),(2782777344,100775421176004,100775801985339)]
theorem point_links_checked21200 : (cuts21200.take 2).map (fun c => (2782658561-1+2*2^9*c.k,100774870509626+c.lower,100775251318641+c.upper)) = pointBounds21200 := by
 decide +kernel
def cuts21201 : List PrefixCut := [⟨73,340461195,340461390⟩,
⟨128,605662652,605663005⟩]
theorem checked21201 : checkPrefixCuts (2^48) 2782789633 9 Manual.Count131072.C021201.packed 128 cuts21201 = true := by
 decide +kernel
def pointBounds21201 : List (Nat × Nat × Nat) := [(2782864384,100775819494251,100776200303811)]
theorem point_links_checked21201 : (cuts21201.take 1).map (fun c => (2782789633-1+2*2^9*c.k,100775479033056+c.lower,100775859842421+c.upper)) = pointBounds21201 := by
 decide +kernel
def cuts21202 : List PrefixCut := [⟨30,148882715,148882797⟩,
⟨115,550918213,550918526⟩,
⟨128,611601718,611602068⟩]
theorem checked21202 : checkPrefixCuts (2^48) 2782920705 9 Manual.Count131072.C021202.packed 128 cuts21202 = true := by
 decide +kernel
def pointBounds21202 : List (Nat × Nat × Nat) := [(2782951424,100776233578423,100776614388223),(2783038464,100776635613921,100777016423952)]
theorem point_links_checked21202 : (cuts21202.take 2).map (fun c => (2782920705-1+2*2^9*c.k,100776084695708+c.lower,100776465505426+c.upper)) = pointBounds21202 := by
 decide +kernel
def cuts21203 : List PrefixCut := [⟨72,348924678,348924880⟩,
⟨128,619056837,619057196⟩]
theorem checked21203 : checkPrefixCuts (2^48) 2783051777 9 Manual.Count131072.C021203.packed 128 cuts21203 = true := by
 decide +kernel
def pointBounds21203 : List (Nat × Nat × Nat) := [(2783125504,100777045222104,100777426032374)]
theorem point_links_checked21203 : (cuts21203.take 1).map (fun c => (2783051777-1+2*2^9*c.k,100776696297426+c.lower,100777077107494+c.upper)) = pointBounds21203 := by
 decide +kernel
def cuts21204 : List PrefixCut := [⟨29,135013412,135013490⟩,
⟨114,536808912,536809221⟩,
⟨128,604464666,604465011⟩]
theorem checked21204 : checkPrefixCuts (2^48) 2783182849 9 Manual.Count131072.C021204.packed 128 cuts21204 = true := by
 decide +kernel
def pointBounds21204 : List (Nat × Nat × Nat) := [(2783212544,100777450367675,100777831178180),(2783299584,100777852163175,100778232973911)]
theorem point_links_checked21204 : (cuts21204.take 2).map (fun c => (2783182849-1+2*2^9*c.k,100777315354263+c.lower,100777696164690+c.upper)) = pointBounds21204 := by
 decide +kernel
def cuts21205 : List PrefixCut := [⟨71,339486979,339487181⟩,
⟨128,612324156,612324516⟩]
theorem checked21205 : checkPrefixCuts (2^48) 2783313921 9 Manual.Count131072.C021205.packed 128 cuts21205 = true := by
 decide +kernel
def pointBounds21205 : List (Nat × Nat × Nat) := [(2783386624,100778259305908,100778640116882)]
theorem point_links_checked21205 : (cuts21205.take 1).map (fun c => (2783313921-1+2*2^9*c.k,100777919818929+c.lower,100778300629701+c.upper)) = pointBounds21205 := by
 decide +kernel
def cuts21206 : List PrefixCut := [⟨28,135506318,135506399⟩,
⟨113,538578625,538578938⟩,
⟨128,609261623,609261978⟩]
theorem checked21206 : checkPrefixCuts (2^48) 2783444993 9 Manual.Count131072.C021206.packed 128 cuts21206 = true := by
 decide +kernel
def pointBounds21206 : List (Nat × Nat × Nat) := [(2783473664,100778667649403,100779048460616),(2783560704,100779070721710,100779451533155)]
theorem point_links_checked21206 : (cuts21206.take 2).map (fun c => (2783444993-1+2*2^9*c.k,100778532143085+c.lower,100778912954217+c.upper)) = pointBounds21206 := by
 decide +kernel
def cuts21207 : List PrefixCut := [⟨70,329242104,329242295⟩,
⟨128,609435112,609435466⟩]
theorem checked21207 : checkPrefixCuts (2^48) 2783576065 9 Manual.Count131072.C021207.packed 128 cuts21207 = true := by
 decide +kernel
def pointBounds21207 : List (Nat × Nat × Nat) := [(2783647744,100779470646812,100779851458490)]
theorem point_links_checked21207 : (cuts21207.take 1).map (fun c => (2783576065-1+2*2^9*c.k,100779141404708+c.lower,100779522216195+c.upper)) = pointBounds21207 := by
 decide +kernel
def cuts21208 : List PrefixCut := [⟨27,125685482,125685556⟩,
⟨112,523158874,523159179⟩,
⟨128,601115198,601115548⟩]
theorem checked21208 : checkPrefixCuts (2^48) 2783707137 9 Manual.Count131072.C021208.packed 128 cuts21208 = true := by
 decide +kernel
def pointBounds21208 : List (Nat × Nat × Nat) := [(2783734784,100779876525302,100780257337217),(2783821824,100780273998694,100780654810840)]
theorem point_links_checked21208 : (cuts21208.take 2).map (fun c => (2783707137-1+2*2^9*c.k,100779750839820+c.lower,100780131651661+c.upper)) = pointBounds21208 := by
 decide +kernel
def cuts21209 : List PrefixCut := [⟨69,325267957,325268148⟩,
⟨128,606344596,606344948⟩]
theorem checked21209 : checkPrefixCuts (2^48) 2783838209 9 Manual.Count131072.C021209.packed 128 cuts21209 = true := by
 decide +kernel
def pointBounds21209 : List (Nat × Nat × Nat) := [(2783908864,100780677222975,100781058035357)]
theorem point_links_checked21209 : (cuts21209.take 1).map (fun c => (2783838209-1+2*2^9*c.k,100780351955018+c.lower,100780732767209+c.upper)) = pointBounds21209 := by
 decide +kernel
def cuts21210 : List PrefixCut := [⟨26,127493567,127493637⟩,
⟨111,527052859,527053161⟩,
⟨128,609753612,609753961⟩]
theorem checked21210 : checkPrefixCuts (2^48) 2783969281 9 Manual.Count131072.C021210.packed 128 cuts21210 = true := by
 decide +kernel
def pointBounds21210 : List (Nat × Nat × Nat) := [(2783995904,100781085793181,100781466605794),(2784082944,100781485352473,100781866165318)]
theorem point_links_checked21210 : (cuts21210.take 2).map (fun c => (2783969281-1+2*2^9*c.k,100780958299614+c.lower,100781339112157+c.upper)) = pointBounds21210 := by
 decide +kernel
def cuts21211 : List PrefixCut := [⟨68,331202254,331202444⟩,
⟨128,615588701,615589059⟩]
theorem checked21211 : checkPrefixCuts (2^48) 2784100353 9 Manual.Count131072.C021211.packed 128 cuts21211 = true := by
 decide +kernel
def pointBounds21211 : List (Nat × Nat × Nat) := [(2784169984,100781899255480,100782280068562)]
theorem point_links_checked21211 : (cuts21211.take 1).map (fun c => (2784100353-1+2*2^9*c.k,100781568053226+c.lower,100781948866118+c.upper)) = pointBounds21211 := by
 decide +kernel
def cuts21212 : List PrefixCut := [⟨25,121618034,121618104⟩,
⟨110,522150769,522151073⟩,
⟨128,607371038,607371392⟩]
theorem checked21212 : checkPrefixCuts (2^48) 2784231425 9 Manual.Count131072.C021212.packed 128 cuts21212 = true := by
 decide +kernel
def pointBounds21212 : List (Nat × Nat × Nat) := [(2784257024,100782305259961,100782686073281),(2784344064,100782705792696,100783086606250)]
theorem point_links_checked21212 : (cuts21212.take 2).map (fun c => (2784231425-1+2*2^9*c.k,100782183641927+c.lower,100782564455177+c.upper)) = pointBounds21212 := by
 decide +kernel
def cuts21213 : List PrefixCut := [⟨67,323184954,323185141⟩,
⟨128,607948960,607949314⟩]
theorem checked21213 : checkPrefixCuts (2^48) 2784362497 9 Manual.Count131072.C021213.packed 128 cuts21213 = true := by
 decide +kernel
def pointBounds21213 : List (Nat × Nat × Nat) := [(2784431104,100783114197919,100783495011710)]
theorem point_links_checked21213 : (cuts21213.take 1).map (fun c => (2784362497-1+2*2^9*c.k,100782791012965+c.lower,100783171826569+c.upper)) = pointBounds21213 := by
 decide +kernel
def cuts21214 : List PrefixCut := [⟨24,112306684,112306751⟩,
⟨109,513913862,513914158⟩,
⟨128,603270495,603270842⟩]
theorem checked21214 : checkPrefixCuts (2^48) 2784493569 9 Manual.Count131072.C021214.packed 128 cuts21214 = true := by
 decide +kernel
def pointBounds21214 : List (Nat × Nat × Nat) := [(2784518144,100783511268609,100783892082634),(2784605184,100783912875787,100784293690041)]
theorem point_links_checked21214 : (cuts21214.take 2).map (fun c => (2784493569-1+2*2^9*c.k,100783398961925+c.lower,100783779775883+c.upper)) = pointBounds21214 := by
 decide +kernel
def cuts21215 : List PrefixCut := [⟨66,316382238,316382418⟩,
⟨128,606982064,606982413⟩]
theorem checked21215 : checkPrefixCuts (2^48) 2784624641 9 Manual.Count131072.C021215.packed 128 cuts21215 = true := by
 decide +kernel
def pointBounds21215 : List (Nat × Nat × Nat) := [(2784692224,100784318614658,100784699429143)]
theorem point_links_checked21215 : (cuts21215.take 1).map (fun c => (2784624641-1+2*2^9*c.k,100784002232420+c.lower,100784383046725+c.upper)) = pointBounds21215 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000037
