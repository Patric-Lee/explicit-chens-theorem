import PlattAssemblyKernel
import PlattCertificates.Count131072.C015152
import PlattCertificates.Count131072.C015153
import PlattCertificates.Count131072.C015154
import PlattCertificates.Count131072.C015155
import PlattCertificates.Count131072.C015156
import PlattCertificates.Count131072.C015157
import PlattCertificates.Count131072.C015158
import PlattCertificates.Count131072.C015159
import PlattCertificates.Count131072.C015160
import PlattCertificates.Count131072.C015161
import PlattCertificates.Count131072.C015162
import PlattCertificates.Count131072.C015163
import PlattCertificates.Count131072.C015164
import PlattCertificates.Count131072.C015165
import PlattCertificates.Count131072.C015166
import PlattCertificates.Count131072.C015167
import PlattCertificates.Count131072.C015168
import PlattCertificates.Count131072.C015169
import PlattCertificates.Count131072.C015170
import PlattCertificates.Count131072.C015171
import PlattCertificates.Count131072.C015172
import PlattCertificates.Count131072.C015173
import PlattCertificates.Count131072.C015174
import PlattCertificates.Count131072.C015175
import PlattCertificates.Count131072.C015176
import PlattCertificates.Count131072.C015177
import PlattCertificates.Count131072.C015178
import PlattCertificates.Count131072.C015179
import PlattCertificates.Count131072.C015180
import PlattCertificates.Count131072.C015181
import PlattCertificates.Count131072.C015182
import PlattCertificates.Count131072.C015183
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000161
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts15152 : List PrefixCut := [⟨23,161817037,161817140⟩,
⟨84,574130337,574130712⟩,
⟨128,870167539,870168110⟩]
theorem checked15152 : checkPrefixCuts (2^48) 1989935105 9 Manual.Count131072.C015152.packed 128 cuts15152 = true := by
 decide +kernel
def pointBounds15152 : List (Nat × Nat × Nat) := [(1989958656,96401266313818,96401644435733),(1990021120,96401678627118,96402056749305)]
theorem point_links_checked15152 : (cuts15152.take 2).map (fun c => (1989935105-1+2*2^9*c.k,96401104496781+c.lower,96401482618593+c.upper)) = pointBounds15152 := by
 decide +kernel
def cuts15153 : List PrefixCut := [⟨17,115414508,115414581⟩,
⟨78,527984823,527985173⟩,
⟨128,866715537,866716111⟩]
theorem checked15153 : checkPrefixCuts (2^48) 1990066177 9 Manual.Count131072.C015153.packed 128 cuts15153 = true := by
 decide +kernel
def pointBounds15153 : List (Nat × Nat × Nat) := [(1990083584,96402090078828,96402468201284),(1990146048,96402502649143,96402880771876)]
theorem point_links_checked15153 : (cuts15153.take 2).map (fun c => (1990066177-1+2*2^9*c.k,96401974664320+c.lower,96402352786703+c.upper)) = pointBounds15153 := by
 decide +kernel
def cuts15154 : List PrefixCut := [⟨11,75099462,75099510⟩,
⟨72,483542479,483542796⟩,
⟨128,856193053,856193615⟩]
theorem checked15154 : checkPrefixCuts (2^48) 1990197249 9 Manual.Count131072.C015154.packed 128 cuts15154 = true := by
 decide +kernel
def pointBounds15154 : List (Nat × Nat × Nat) := [(1990208512,96402916479319,96403294602324),(1990270976,96403324922336,96403703045610)]
theorem point_links_checked15154 : (cuts15154.take 2).map (fun c => (1990197249-1+2*2^9*c.k,96402841379857+c.lower,96403219502814+c.upper)) = pointBounds15154 := by
 decide +kernel
def cuts15155 : List PrefixCut := [⟨5,34931024,34931046⟩,
⟨66,447166654,447166946⟩,
⟨127,856702583,856703149⟩,
⟨128,863490362,863490932⟩]
theorem checked15155 : checkPrefixCuts (2^48) 1990328321 9 Manual.Count131072.C015155.packed 128 cuts15155 = true := by
 decide +kernel
def pointBounds15155 : List (Nat × Nat × Nat) := [(1990333440,96403732503934,96404110627475),(1990395904,96404144739564,96404522863375),(1990458368,96404554275493,96404932399578)]
theorem point_links_checked15155 : (cuts15155.take 3).map (fun c => (1990328321-1+2*2^9*c.k,96403697572910+c.lower,96404075696429+c.upper)) = pointBounds15155 := by
 decide +kernel
def cuts15156 : List PrefixCut := [⟨60,404007940,404008209⟩,
⟨121,817194637,817195175⟩,
⟨128,866261466,866262035⟩]
theorem checked15156 : checkPrefixCuts (2^48) 1990459393 9 Manual.Count131072.C015156.packed 128 cuts15156 = true := by
 decide +kernel
def pointBounds15156 : List (Nat × Nat × Nat) := [(1990520832,96404965071212,96405343195570),(1990583296,96405378257909,96405756382536)]
theorem point_links_checked15156 : (cuts15156.take 2).map (fun c => (1990459393-1+2*2^9*c.k,96404561063272+c.lower,96404939187361+c.upper)) = pointBounds15156 := by
 decide +kernel
def cuts15157 : List PrefixCut := [⟨54,367359096,367359338⟩,
⟨115,787589668,787590181⟩,
⟨128,871719023,871719591⟩]
theorem checked15157 : checkPrefixCuts (2^48) 1990590465 9 Manual.Count131072.C015157.packed 128 cuts15157 = true := by
 decide +kernel
def pointBounds15157 : List (Nat × Nat × Nat) := [(1990645760,96405794683834,96406172808734),(1990708224,96406214914406,96406593039577)]
theorem point_links_checked15157 : (cuts15157.take 2).map (fun c => (1990590465-1+2*2^9*c.k,96405427324738+c.lower,96405805449396+c.upper)) = pointBounds15157 := by
 decide +kernel
def cuts15158 : List PrefixCut := [⟨48,320393395,320393611⟩,
⟨109,730983222,730983709⟩,
⟨128,857239833,857240405⟩]
theorem checked15158 : checkPrefixCuts (2^48) 1990721537 9 Manual.Count131072.C015158.packed 128 cuts15158 = true := by
 decide +kernel
def pointBounds15158 : List (Nat × Nat × Nat) := [(1990770688,96406619437156,96406997562598),(1990833152,96407030026983,96407408152696)]
theorem point_links_checked15158 : (cuts15158.take 2).map (fun c => (1990721537-1+2*2^9*c.k,96406299043761+c.lower,96406677168987+c.upper)) = pointBounds15158 := by
 decide +kernel
def cuts15159 : List PrefixCut := [⟨42,291530802,291530993⟩,
⟨103,705487900,705488363⟩,
⟨128,865666549,865667122⟩]
theorem checked15159 : checkPrefixCuts (2^48) 1990852609 9 Manual.Count131072.C015159.packed 128 cuts15159 = true := by
 decide +kernel
def pointBounds15159 : List (Nat × Nat × Nat) := [(1990895616,96407447814396,96407825940385),(1990958080,96407861771494,96408239897755)]
theorem point_links_checked15159 : (cuts15159.take 2).map (fun c => (1990852609-1+2*2^9*c.k,96407156283594+c.lower,96407534409392+c.upper)) = pointBounds15159 := by
 decide +kernel
def cuts15160 : List PrefixCut := [⟨36,245424351,245424520⟩,
⟨97,654690293,654690739⟩,
⟨128,863206005,863206585⟩]
theorem checked15160 : checkPrefixCuts (2^48) 1990983681 9 Manual.Count131072.C015160.packed 128 cuts15160 = true := by
 decide +kernel
def pointBounds15160 : List (Nat × Nat × Nat) := [(1991020544,96408267374494,96408645501034),(1991083008,96408676640436,96409054767253)]
theorem point_links_checked15160 : (cuts15160.take 2).map (fun c => (1990983681-1+2*2^9*c.k,96408021950143+c.lower,96408400076514+c.upper)) = pointBounds15160 := by
 decide +kernel
def cuts15161 : List PrefixCut := [⟨30,196072389,196072519⟩,
⟨91,611532612,611533010⟩,
⟨128,868237875,868238447⟩]
theorem checked15161 : checkPrefixCuts (2^48) 1991114753 9 Manual.Count131072.C015161.packed 128 cuts15161 = true := by
 decide +kernel
def pointBounds15161 : List (Nat × Nat × Nat) := [(1991145472,96409081228537,96409459355618),(1991207936,96409496688760,96409874816109)]
theorem point_links_checked15161 : (cuts15161.take 2).map (fun c => (1991114753-1+2*2^9*c.k,96408885156148+c.lower,96409263283099+c.upper)) = pointBounds15161 := by
 decide +kernel
def cuts15162 : List PrefixCut := [⟨24,164537557,164537661⟩,
⟨85,576296570,576296941⟩,
⟨128,870442667,870443233⟩]
theorem checked15162 : checkPrefixCuts (2^48) 1991245825 9 Manual.Count131072.C015162.packed 128 cuts15162 = true := by
 decide +kernel
def pointBounds15162 : List (Nat × Nat × Nat) := [(1991270400,96409917931580,96410296059207),(1991332864,96410329690593,96410707818487)]
theorem point_links_checked15162 : (cuts15162.take 2).map (fun c => (1991245825-1+2*2^9*c.k,96409753394023+c.lower,96410131521546+c.upper)) = pointBounds15162 := by
 decide +kernel
def cuts15163 : List PrefixCut := [⟨18,123960629,123960714⟩,
⟨79,536541789,536542147⟩,
⟨128,865297135,865297709⟩]
theorem checked15163 : checkPrefixCuts (2^48) 1991376897 9 Manual.Count131072.C015163.packed 128 cuts15163 = true := by
 decide +kernel
def pointBounds15163 : List (Nat × Nat × Nat) := [(1991395328,96410747797319,96411125925493),(1991457792,96411160378479,96411538506926)]
theorem point_links_checked15163 : (cuts15163.take 2).map (fun c => (1991376897-1+2*2^9*c.k,96410623836690+c.lower,96411001964779+c.upper)) = pointBounds15163 := by
 decide +kernel
def cuts15164 : List PrefixCut := [⟨12,83671581,83671636⟩,
⟨73,492269584,492269911⟩,
⟨128,870893331,870893909⟩]
theorem checked15164 : checkPrefixCuts (2^48) 1991507969 9 Manual.Count131072.C015164.packed 128 cuts15164 = true := by
 decide +kernel
def pointBounds15164 : List (Nat × Nat × Nat) := [(1991520256,96411572805406,96411950934124),(1991582720,96411981403409,96412359532399)]
theorem point_links_checked15164 : (cuts15164.take 2).map (fun c => (1991507969-1+2*2^9*c.k,96411489133825+c.lower,96411867262488+c.upper)) = pointBounds15164 := by
 decide +kernel
def cuts15165 : List PrefixCut := [⟨6,39854505,39854531⟩,
⟨67,455493084,455493387⟩,
⟨128,865889837,865890406⟩]
theorem checked15165 : checkPrefixCuts (2^48) 1991639041 9 Manual.Count131072.C015165.packed 128 cuts15165 = true := by
 decide +kernel
def pointBounds15165 : List (Nat × Nat × Nat) := [(1991645184,96412399881661,96412778010928),(1991707648,96412815520240,96413193649784),(1991770112,96413225916993,96413604046803)]
theorem point_links_checked15165 : (cuts15165.take 3).map (fun c => (1991639041-1+2*2^9*c.k,96412360027156+c.lower,96412738156397+c.upper)) = pointBounds15165 := by
 decide +kernel
def cuts15166 : List PrefixCut := [⟨61,408405417,408405688⟩,
⟨122,813689188,813689725⟩,
⟨128,851842857,851843420⟩]
theorem checked15166 : checkPrefixCuts (2^48) 1991770113 9 Manual.Count131072.C015166.packed 128 cuts15166 = true := by
 decide +kernel
def pointBounds15166 : List (Nat × Nat × Nat) := [(1991832576,96413634322410,96414012452491),(1991895040,96414039606181,96414417736528)]
theorem point_links_checked15166 : (cuts15166.take 2).map (fun c => (1991770113-1+2*2^9*c.k,96413225916993+c.lower,96413604046803+c.upper)) = pointBounds15166 := by
 decide +kernel
def cuts15167 : List PrefixCut := [⟨55,374182704,374182955⟩,
⟨116,783821362,783821891⟩,
⟨128,865634521,865635106⟩]
theorem checked15167 : checkPrefixCuts (2^48) 1991901185 9 Manual.Count131072.C015167.packed 128 cuts15167 = true := by
 decide +kernel
def pointBounds15167 : List (Nat × Nat × Nat) := [(1991957504,96414451942554,96414830073178),(1992019968,96414861581212,96415239712114)]
theorem point_links_checked15167 : (cuts15167.take 2).map (fun c => (1991901185-1+2*2^9*c.k,96414077759850+c.lower,96414455890223+c.upper)) = pointBounds15167 := by
 decide +kernel
def cuts15168 : List PrefixCut := [⟨49,331910358,331910580⟩,
⟨110,742229898,742230386⟩,
⟨128,863175611,863176181⟩]
theorem checked15168 : checkPrefixCuts (2^48) 1992032257 9 Manual.Count131072.C015168.packed 128 cuts15168 = true := by
 decide +kernel
def pointBounds15168 : List (Nat × Nat × Nat) := [(1992082432,96415275304729,96415653435909),(1992144896,96415685624269,96416063755715)]
theorem point_links_checked15168 : (cuts15168.take 2).map (fun c => (1992032257-1+2*2^9*c.k,96414943394371+c.lower,96415321525329+c.upper)) = pointBounds15168 := by
 decide +kernel
def cuts15169 : List PrefixCut := [⟨43,293175732,293175929⟩,
⟨104,710392506,710392981⟩,
⟨128,872443692,872444276⟩]
theorem checked15169 : checkPrefixCuts (2^48) 1992163329 9 Manual.Count131072.C015169.packed 128 cuts15169 = true := by
 decide +kernel
def pointBounds15169 : List (Nat × Nat × Nat) := [(1992207360,96416099745714,96416477877439),(1992269824,96416516962488,96416895094491)]
theorem point_links_checked15169 : (cuts15169.take 2).map (fun c => (1992163329-1+2*2^9*c.k,96415806569982+c.lower,96416184701510+c.upper)) = pointBounds15169 := by
 decide +kernel
def cuts15170 : List PrefixCut := [⟨37,244556396,244556557⟩,
⟨98,654824403,654824837⟩,
⟨128,859388551,859389119⟩]
theorem checked15170 : checkPrefixCuts (2^48) 1992294401 9 Manual.Count131072.C015170.packed 128 cuts15170 = true := by
 decide +kernel
def pointBounds15170 : List (Nat × Nat × Nat) := [(1992332288,96416923570070,96417301702343),(1992394752,96417333838077,96417711970623)]
theorem point_links_checked15170 : (cuts15170.take 2).map (fun c => (1992294401-1+2*2^9*c.k,96416679013674+c.lower,96417057145786+c.upper)) = pointBounds15170 := by
 decide +kernel
def cuts15171 : List PrefixCut := [⟨31,210494304,210494443⟩,
⟨92,623279420,623279834⟩,
⟨128,868514569,868515145⟩]
theorem checked15171 : checkPrefixCuts (2^48) 1992425473 9 Manual.Count131072.C015171.packed 128 cuts15171 = true := by
 decide +kernel
def pointBounds15171 : List (Nat × Nat × Nat) := [(1992457216,96417748896529,96418127029348),(1992519680,96418161681645,96418539814739)]
theorem point_links_checked15171 : (cuts15171.take 2).map (fun c => (1992425473-1+2*2^9*c.k,96417538402225+c.lower,96417916534905+c.upper)) = pointBounds15171 := by
 decide +kernel
def cuts15172 : List PrefixCut := [⟨25,168808439,168808550⟩,
⟨86,578318736,578319111⟩,
⟨128,865632247,865632809⟩]
theorem checked15172 : checkPrefixCuts (2^48) 1992556545 9 Manual.Count131072.C015172.packed 128 cuts15172 = true := by
 decide +kernel
def pointBounds15172 : List (Nat × Nat × Nat) := [(1992582144,96418575725233,96418953858600),(1992644608,96418985235530,96419363369161)]
theorem point_links_checked15172 : (cuts15172.take 2).map (fun c => (1992556545-1+2*2^9*c.k,96418406916794+c.lower,96418785050050+c.upper)) = pointBounds15172 := by
 decide +kernel
def cuts15173 : List PrefixCut := [⟨19,126986621,126986708⟩,
⟨80,532798683,532799038⟩,
⟨128,854275324,854275892⟩]
theorem checked15173 : checkPrefixCuts (2^48) 1992687617 9 Manual.Count131072.C015173.packed 128 cuts15173 = true := by
 decide +kernel
def pointBounds15173 : List (Nat × Nat × Nat) := [(1992707072,96419399535662,96419777669567),(1992769536,96419805347724,96420183481897)]
theorem point_links_checked15173 : (cuts15173.take 2).map (fun c => (1992687617-1+2*2^9*c.k,96419272549041+c.lower,96419650682859+c.upper)) = pointBounds15173 := by
 decide +kernel
def cuts15174 : List PrefixCut := [⟨13,94774813,94774872⟩,
⟨74,510730868,510731204⟩,
⟨128,886280861,886281446⟩]
theorem checked15174 : checkPrefixCuts (2^48) 1992818689 9 Manual.Count131072.C015174.packed 128 cuts15174 = true := by
 decide +kernel
def pointBounds15174 : List (Nat × Nat × Nat) := [(1992832000,96420221599178,96420599733623),(1992894464,96420637555233,96421015689955)]
theorem point_links_checked15174 : (cuts15174.take 2).map (fun c => (1992818689-1+2*2^9*c.k,96420126824365+c.lower,96420504958751+c.upper)) = pointBounds15174 := by
 decide +kernel
def cuts15175 : List PrefixCut := [⟨7,42511752,42511782⟩,
⟨68,465220930,465221241⟩,
⟨128,867721283,867721867⟩]
theorem checked15175 : checkPrefixCuts (2^48) 1992949761 9 Manual.Count131072.C015175.packed 128 cuts15175 = true := by
 decide +kernel
def pointBounds15175 : List (Nat × Nat × Nat) := [(1992956928,96421055616978,96421433751979),(1993019392,96421478326156,96421856461438)]
theorem point_links_checked15175 : (cuts15175.take 2).map (fun c => (1992949761-1+2*2^9*c.k,96421013105226+c.lower,96421391240197+c.upper)) = pointBounds15175 := by
 decide +kernel
def cuts15176 : List PrefixCut := [⟨1,7343751,7343756⟩,
⟨62,416468871,416469147⟩,
⟨123,824592676,824593226⟩,
⟨128,857778652,857779224⟩]
theorem checked15176 : checkPrefixCuts (2^48) 1993080833 9 Manual.Count131072.C015176.packed 128 cuts15176 = true := by
 decide +kernel
def pointBounds15176 : List (Nat × Nat × Nat) := [(1993081856,96421888170260,96422266305820),(1993144320,96422297295380,96422675431211),(1993206784,96422705419185,96423083555290)]
theorem point_links_checked15176 : (cuts15176.take 3).map (fun c => (1993080833-1+2*2^9*c.k,96421880826509+c.lower,96422258962064+c.upper)) = pointBounds15176 := by
 decide +kernel
def cuts15177 : List PrefixCut := [⟨56,377043223,377043480⟩,
⟨117,780340347,780340878⟩,
⟨128,849814606,849815185⟩]
theorem checked15177 : checkPrefixCuts (2^48) 1993211905 9 Manual.Count131072.C015177.packed 128 cuts15177 = true := by
 decide +kernel
def pointBounds15177 : List (Nat × Nat × Nat) := [(1993269248,96423115648384,96423493784768),(1993331712,96423518945508,96423897082166)]
theorem point_links_checked15177 : (cuts15177.take 2).map (fun c => (1993211905-1+2*2^9*c.k,96422738605161+c.lower,96423116741288+c.upper)) = pointBounds15177 := by
 decide +kernel
def cuts15178 : List PrefixCut := [⟨50,342564896,342565124⟩,
⟨111,752190787,752191282⟩,
⟨128,863737837,863738405⟩]
theorem checked15178 : checkPrefixCuts (2^48) 1993342977 9 Manual.Count131072.C015178.packed 128 cuts15178 = true := by
 decide +kernel
def pointBounds15178 : List (Nat × Nat × Nat) := [(1993394176,96423930984663,96424309121597),(1993456640,96424340610554,96424718747755)]
theorem point_links_checked15178 : (cuts15178.take 2).map (fun c => (1993342977-1+2*2^9*c.k,96423588419767+c.lower,96423966556473+c.upper)) = pointBounds15178 := by
 decide +kernel
def cuts15179 : List PrefixCut := [⟨44,305690567,305690770⟩,
⟨105,717691061,717691544⟩,
⟨128,870458349,870458933⟩]
theorem checked15179 : checkPrefixCuts (2^48) 1993474049 9 Manual.Count131072.C015179.packed 128 cuts15179 = true := by
 decide +kernel
def pointBounds15179 : List (Nat × Nat × Nat) := [(1993519104,96424757848171,96425135985648),(1993581568,96425169848665,96425547986422)]
theorem point_links_checked15179 : (cuts15179.take 2).map (fun c => (1993474049-1+2*2^9*c.k,96424452157604+c.lower,96424830294878+c.upper)) = pointBounds15179 := by
 decide +kernel
def cuts15180 : List PrefixCut := [⟨38,259643812,259643984⟩,
⟨99,680513061,680513506⟩,
⟨128,874777655,874778230⟩]
theorem checked15180 : checkPrefixCuts (2^48) 1993605121 9 Manual.Count131072.C015180.packed 128 cuts15180 = true := by
 decide +kernel
def pointBounds15180 : List (Nat × Nat × Nat) := [(1993644032,96425582259765,96425960397795),(1993706496,96426003129014,96426381267317)]
theorem point_links_checked15180 : (cuts15180.take 2).map (fun c => (1993605121-1+2*2^9*c.k,96425322615953+c.lower,96425700753811+c.upper)) = pointBounds15180 := by
 decide +kernel
def cuts15181 : List PrefixCut := [⟨32,214591216,214591359⟩,
⟨93,629222387,629222794⟩,
⟨128,859190898,859191456⟩]
theorem checked15181 : checkPrefixCuts (2^48) 1993736193 9 Manual.Count131072.C015181.packed 128 cuts15181 = true := by
 decide +kernel
def pointBounds15181 : List (Nat × Nat × Nat) := [(1993768960,96426411984824,96426790123400),(1993831424,96426826615995,96427204754835)]
theorem point_links_checked15181 : (cuts15181.take 2).map (fun c => (1993736193-1+2*2^9*c.k,96426197393608+c.lower,96426575532041+c.upper)) = pointBounds15181 := by
 decide +kernel
def cuts15182 : List PrefixCut := [⟨26,171803143,171803258⟩,
⟨87,587537804,587538195⟩,
⟨128,858146424,858146995⟩]
theorem checked15182 : checkPrefixCuts (2^48) 1993867265 9 Manual.Count131072.C015182.packed 128 cuts15182 = true := by
 decide +kernel
def pointBounds15182 : List (Nat × Nat × Nat) := [(1993893888,96427228387649,96427606526755),(1993956352,96427644122310,96428022261692)]
theorem point_links_checked15182 : (cuts15182.take 2).map (fun c => (1993867265-1+2*2^9*c.k,96427056584506+c.lower,96427434723497+c.upper)) = pointBounds15182 := by
 decide +kernel
def cuts15183 : List PrefixCut := [⟨20,134102310,134102399⟩,
⟨81,544305616,544305977⟩,
⟨128,864018248,864018828⟩]
theorem checked15183 : checkPrefixCuts (2^48) 1993998337 9 Manual.Count131072.C015183.packed 128 cuts15183 = true := by
 decide +kernel
def pointBounds15183 : List (Nat × Nat × Nat) := [(1994018816,96428048833240,96428426972891),(1994081280,96428459036546,96428837176469)]
theorem point_links_checked15183 : (cuts15183.take 2).map (fun c => (1993998337-1+2*2^9*c.k,96427914730930+c.lower,96428292870492+c.upper)) = pointBounds15183 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000161
