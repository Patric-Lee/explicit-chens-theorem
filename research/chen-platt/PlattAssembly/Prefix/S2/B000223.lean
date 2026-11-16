import PlattAssemblyKernel
import PlattCertificates.Count131072.C017136
import PlattCertificates.Count131072.C017137
import PlattCertificates.Count131072.C017138
import PlattCertificates.Count131072.C017139
import PlattCertificates.Count131072.C017140
import PlattCertificates.Count131072.C017141
import PlattCertificates.Count131072.C017142
import PlattCertificates.Count131072.C017143
import PlattCertificates.Count131072.C017144
import PlattCertificates.Count131072.C017145
import PlattCertificates.Count131072.C017146
import PlattCertificates.Count131072.C017147
import PlattCertificates.Count131072.C017148
import PlattCertificates.Count131072.C017149
import PlattCertificates.Count131072.C017150
import PlattCertificates.Count131072.C017151
import PlattCertificates.Count131072.C017152
import PlattCertificates.Count131072.C017153
import PlattCertificates.Count131072.C017154
import PlattCertificates.Count131072.C017155
import PlattCertificates.Count131072.C017156
import PlattCertificates.Count131072.C017157
import PlattCertificates.Count131072.C017158
import PlattCertificates.Count131072.C017159
import PlattCertificates.Count131072.C017160
import PlattCertificates.Count131072.C017161
import PlattCertificates.Count131072.C017162
import PlattCertificates.Count131072.C017163
import PlattCertificates.Count131072.C017164
import PlattCertificates.Count131072.C017165
import PlattCertificates.Count131072.C017166
import PlattCertificates.Count131072.C017167
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000223
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts17136 : List PrefixCut := [⟨15,85693853,85693909⟩,
⟨84,501645175,501645486⟩,
⟨128,766971493,766971966⟩]
theorem checked17136 : checkPrefixCuts (2^48) 2249981953 9 Manual.Count131072.C017136.packed 128 cuts17136 = true := by
 decide +kernel
def pointBounds17136 : List (Nat × Nat × Nat) := [(2249997312,98011142753372,98011521908458),(2250067968,98011558704694,98011937860035)]
theorem point_links_checked17136 : (cuts17136.take 2).map (fun c => (2249981953-1+2*2^9*c.k,98011057059519+c.lower,98011436214549+c.upper)) = pointBounds17136 := by
 decide +kernel
def cuts17137 : List PrefixCut := [⟨25,153113797,153113890⟩,
⟨94,564410695,564411045⟩,
⟨128,763424643,763425116⟩]
theorem checked17137 : checkPrefixCuts (2^48) 2250113025 9 Manual.Count131072.C017137.packed 128 cuts17137 = true := by
 decide +kernel
def pointBounds17137 : List (Nat × Nat × Nat) := [(2250138624,98011977144809,98012356300405),(2250209280,98012388441707,98012767597560)]
theorem point_links_checked17137 : (cuts17137.take 2).map (fun c => (2250113025-1+2*2^9*c.k,98011824031012+c.lower,98012203186515+c.upper)) = pointBounds17137 := by
 decide +kernel
def cuts17138 : List PrefixCut := [⟨35,207141374,207141504⟩,
⟨104,617912043,617912433⟩,
⟨128,757501082,757501558⟩]
theorem checked17138 : checkPrefixCuts (2^48) 2250244097 9 Manual.Count131072.C017138.packed 128 cuts17138 = true := by
 decide +kernel
def pointBounds17138 : List (Nat × Nat × Nat) := [(2250279936,98012794597029,98013173753135),(2250350592,98013205367698,98013584524064)]
theorem point_links_checked17138 : (cuts17138.take 2).map (fun c => (2250244097-1+2*2^9*c.k,98012587455655+c.lower,98012966611631+c.upper)) = pointBounds17138 := by
 decide +kernel
def cuts17139 : List PrefixCut := [⟨45,268166800,268166969⟩,
⟨114,681413141,681413571⟩,
⟨128,764836312,764836794⟩]
theorem checked17139 : checkPrefixCuts (2^48) 2250375169 9 Manual.Count131072.C017139.packed 128 cuts17139 = true := by
 decide +kernel
def pointBounds17139 : List (Nat × Nat × Nat) := [(2250421248,98013613123537,98013992280158),(2250491904,98014026369878,98014405526760)]
theorem point_links_checked17139 : (cuts17139.take 2).map (fun c => (2250375169-1+2*2^9*c.k,98013344956737+c.lower,98013724113189+c.upper)) = pointBounds17139 := by
 decide +kernel
def cuts17140 : List PrefixCut := [⟨55,323431647,323431849⟩,
⟨124,745531852,745532315⟩,
⟨128,768543746,768544224⟩]
theorem checked17140 : checkPrefixCuts (2^48) 2250506241 9 Manual.Count131072.C017140.packed 128 cuts17140 = true := by
 decide +kernel
def pointBounds17140 : List (Nat × Nat × Nat) := [(2250562560,98014433224696,98014812381832),(2250633216,98014855324901,98015234482298)]
theorem point_links_checked17140 : (cuts17140.take 2).map (fun c => (2250506241-1+2*2^9*c.k,98014109793049+c.lower,98014488949983+c.upper)) = pointBounds17140 := by
 decide +kernel
def cuts17141 : List PrefixCut := [⟨65,390945901,390946139⟩,
⟨128,771125357,771125834⟩]
theorem checked17141 : checkPrefixCuts (2^48) 2250637313 9 Manual.Count131072.C017141.packed 128 cuts17141 = true := by
 decide +kernel
def pointBounds17141 : List (Nat × Nat × Nat) := [(2250703872,98015269282696,98015648440346)]
theorem point_links_checked17141 : (cuts17141.take 1).map (fun c => (2250637313-1+2*2^9*c.k,98014878336795+c.lower,98015257494207+c.upper)) = pointBounds17141 := by
 decide +kernel
def cuts17142 : List PrefixCut := [⟨6,35015980,35016003⟩,
⟨75,448447622,448447899⟩,
⟨128,762951967,762952440⟩]
theorem checked17142 : checkPrefixCuts (2^48) 2250768385 9 Manual.Count131072.C017142.packed 128 cuts17142 = true := by
 decide +kernel
def pointBounds17142 : List (Nat × Nat × Nat) := [(2250774528,98015684478132,98016063636044),(2250845184,98016097909774,98016477067940)]
theorem point_links_checked17142 : (cuts17142.take 2).map (fun c => (2250768385-1+2*2^9*c.k,98015649462152+c.lower,98016028620041+c.upper)) = pointBounds17142 := by
 decide +kernel
def cuts17143 : List PrefixCut := [⟨16,94287334,94287393⟩,
⟨85,493437602,493437917⟩,
⟨128,751528239,751528714⟩]
theorem checked17143 : checkPrefixCuts (2^48) 2250899457 9 Manual.Count131072.C017143.packed 128 cuts17143 = true := by
 decide +kernel
def pointBounds17143 : List (Nat × Nat × Nat) := [(2250915840,98016506701453,98016885859874),(2250986496,98016905851721,98017285010398)]
theorem point_links_checked17143 : (cuts17143.take 2).map (fun c => (2250899457-1+2*2^9*c.k,98016412414119+c.lower,98016791572481+c.upper)) = pointBounds17143 := by
 decide +kernel
def cuts17144 : List PrefixCut := [⟨26,152176055,152176148⟩,
⟨95,568056630,568056986⟩,
⟨128,768864971,768865452⟩]
theorem checked17144 : checkPrefixCuts (2^48) 2251030529 9 Manual.Count131072.C017144.packed 128 cuts17144 = true := by
 decide +kernel
def pointBounds17144 : List (Nat × Nat × Nat) := [(2251057152,98017316118413,98017695277343),(2251127808,98017731998988,98018111158181)]
theorem point_links_checked17144 : (cuts17144.take 2).map (fun c => (2251030529-1+2*2^9*c.k,98017163942358+c.lower,98017543101195+c.upper)) = pointBounds17144 := by
 decide +kernel
def cuts17145 : List PrefixCut := [⟨36,218310026,218310165⟩,
⟨105,637790329,637790731⟩,
⟨128,772696378,772696862⟩]
theorem checked17145 : checkPrefixCuts (2^48) 2251161601 9 Manual.Count131072.C017145.packed 128 cuts17145 = true := by
 decide +kernel
def pointBounds17145 : List (Nat × Nat × Nat) := [(2251198464,98018151117355,98018530276812),(2251269120,98018570597658,98018949757378)]
theorem point_links_checked17145 : (cuts17145.take 2).map (fun c => (2251161601-1+2*2^9*c.k,98017932807329+c.lower,98018311966647+c.upper)) = pointBounds17145 := by
 decide +kernel
def cuts17146 : List PrefixCut := [⟨46,272433403,272433573⟩,
⟨115,677259616,677260038⟩,
⟨128,757148172,757148642⟩]
theorem checked17146 : checkPrefixCuts (2^48) 2251292673 9 Manual.Count131072.C017146.packed 128 cuts17146 = true := by
 decide +kernel
def pointBounds17146 : List (Nat × Nat × Nat) := [(2251339776,98018977937110,98019357097082),(2251410432,98019382763323,98019761923547)]
theorem point_links_checked17146 : (cuts17146.take 2).map (fun c => (2251292673-1+2*2^9*c.k,98018705503707+c.lower,98019084663509+c.upper)) = pointBounds17146 := by
 decide +kernel
def cuts17147 : List PrefixCut := [⟨56,333926451,333926659⟩,
⟨125,752854112,752854576⟩,
⟨128,770981091,770981566⟩]
theorem checked17147 : checkPrefixCuts (2^48) 2251423745 9 Manual.Count131072.C017147.packed 128 cuts17147 = true := by
 decide +kernel
def pointBounds17147 : List (Nat × Nat × Nat) := [(2251481088,98019796578330,98020175738810),(2251551744,98020215505991,98020594666727)]
theorem point_links_checked17147 : (cuts17147.take 2).map (fun c => (2251423745-1+2*2^9*c.k,98019462651879+c.lower,98019841812151+c.upper)) = pointBounds17147 := by
 decide +kernel
def cuts17148 : List PrefixCut := [⟨66,392161719,392161960⟩,
⟨128,757435222,757435685⟩]
theorem checked17148 : checkPrefixCuts (2^48) 2251554817 9 Manual.Count131072.C017148.packed 128 cuts17148 = true := by
 decide +kernel
def pointBounds17148 : List (Nat × Nat × Nat) := [(2251622400,98020625794689,98021004955677)]
theorem point_links_checked17148 : (cuts17148.take 1).map (fun c => (2251554817-1+2*2^9*c.k,98020233632970+c.lower,98020612793717+c.upper)) = pointBounds17148 := by
 decide +kernel
def cuts17149 : List PrefixCut := [⟨7,40876990,40877017⟩,
⟨76,441389562,441389843⟩,
⟨128,760390767,760391255⟩]
theorem checked17149 : checkPrefixCuts (2^48) 2251685889 9 Manual.Count131072.C017149.packed 128 cuts17149 = true := by
 decide +kernel
def pointBounds17149 : List (Nat × Nat × Nat) := [(2251693056,98021031945182,98021411106419),(2251763712,98021432457754,98021811619245)]
theorem point_links_checked17149 : (cuts17149.take 2).map (fun c => (2251685889-1+2*2^9*c.k,98020991068192+c.lower,98021370229402+c.upper)) = pointBounds17149 := by
 decide +kernel
def cuts17150 : List PrefixCut := [⟨17,102248788,102248855⟩,
⟨86,504736141,504736461⟩,
⟨128,749972263,749972736⟩]
theorem checked17150 : checkPrefixCuts (2^48) 2251816961 9 Manual.Count131072.C017150.packed 128 cuts17150 = true := by
 decide +kernel
def pointBounds17150 : List (Nat × Nat × Nat) := [(2251834368,98021853707747,98022232869512),(2251905024,98022256195100,98022635357118)]
theorem point_links_checked17150 : (cuts17150.take 2).map (fun c => (2251816961-1+2*2^9*c.k,98021751458959+c.lower,98022130620657+c.upper)) = pointBounds17150 := by
 decide +kernel
def cuts17151 : List PrefixCut := [⟨27,161613336,161613436⟩,
⟨96,570574850,570575206⟩,
⟨128,765676991,765677469⟩]
theorem checked17151 : checkPrefixCuts (2^48) 2251948033 9 Manual.Count131072.C017151.packed 128 cuts17151 = true := by
 decide +kernel
def pointBounds17151 : List (Nat × Nat × Nat) := [(2251975680,98022663044558,98023042206829),(2252046336,98023072006072,98023451168599)]
theorem point_links_checked17151 : (cuts17151.take 2).map (fun c => (2251948033-1+2*2^9*c.k,98022501431222+c.lower,98022880593393+c.upper)) = pointBounds17151 := by
 decide +kernel
def cuts17152 : List PrefixCut := [⟨37,222095483,222095624⟩,
⟨106,630406477,630406868⟩,
⟨128,766757269,766757745⟩]
theorem checked17152 : checkPrefixCuts (2^48) 2252079105 9 Manual.Count131072.C017152.packed 128 cuts17152 = true := by
 decide +kernel
def pointBounds17152 : List (Nat × Nat × Nat) := [(2252116992,98023489203696,98023868366486),(2252187648,98023897514690,98024276677730)]
theorem point_links_checked17152 : (cuts17152.take 2).map (fun c => (2252079105-1+2*2^9*c.k,98023267108213+c.lower,98023646270862+c.upper)) = pointBounds17152 := by
 decide +kernel
def cuts17153 : List PrefixCut := [⟨47,280570781,280570954⟩,
⟨116,685481941,685482363⟩,
⟨128,753340786,753341250⟩]
theorem checked17153 : checkPrefixCuts (2^48) 2252210177 9 Manual.Count131072.C017153.packed 128 cuts17153 = true := by
 decide +kernel
def pointBounds17153 : List (Nat × Nat × Nat) := [(2252258304,98024314436263,98024693599561),(2252328960,98024719347423,98025098510970)]
theorem point_links_checked17153 : (cuts17153.take 2).map (fun c => (2252210177-1+2*2^9*c.k,98024033865482+c.lower,98024413028607+c.upper)) = pointBounds17153 := by
 decide +kernel
def cuts17154 : List PrefixCut := [⟨57,341663345,341663550⟩,
⟨126,750922811,750923270⟩,
⟨128,763544044,763544511⟩]
theorem checked17154 : checkPrefixCuts (2^48) 2252341249 9 Manual.Count131072.C017154.packed 128 cuts17154 = true := by
 decide +kernel
def pointBounds17154 : List (Nat × Nat × Nat) := [(2252399616,98025128869613,98025508033407),(2252470272,98025538129079,98025917293127)]
theorem point_links_checked17154 : (cuts17154.take 2).map (fun c => (2252341249-1+2*2^9*c.k,98024787206268+c.lower,98025166369857+c.upper)) = pointBounds17154 := by
 decide +kernel
def cuts17155 : List PrefixCut := [⟨67,394875962,394876210⟩,
⟨128,755127280,755127745⟩]
theorem checked17155 : checkPrefixCuts (2^48) 2252472321 9 Manual.Count131072.C017155.packed 128 cuts17155 = true := by
 decide +kernel
def pointBounds17155 : List (Nat × Nat × Nat) := [(2252540928,98025945626274,98026324790578)]
theorem point_links_checked17155 : (cuts17155.take 1).map (fun c => (2252472321-1+2*2^9*c.k,98025550750312+c.lower,98025929914368+c.upper)) = pointBounds17155 := by
 decide +kernel
def cuts17156 : List PrefixCut := [⟨8,50231967,50231999⟩,
⟨77,453080301,453080584⟩,
⟨128,759831423,759831899⟩]
theorem checked17156 : checkPrefixCuts (2^48) 2252603393 9 Manual.Count131072.C017156.packed 128 cuts17156 = true := by
 decide +kernel
def pointBounds17156 : List (Nat × Nat × Nat) := [(2252611584,98026356109559,98026735274112),(2252682240,98026758957893,98027138122697)]
theorem point_links_checked17156 : (cuts17156.take 2).map (fun c => (2252603393-1+2*2^9*c.k,98026305877592+c.lower,98026685042113+c.upper)) = pointBounds17156 := by
 decide +kernel
def cuts17157 : List PrefixCut := [⟨18,108329565,108329633⟩,
⟨87,522147796,522148116⟩,
⟨128,767034147,767034622⟩]
theorem checked17157 : checkPrefixCuts (2^48) 2252734465 9 Manual.Count131072.C017157.packed 128 cuts17157 = true := by
 decide +kernel
def pointBounds17157 : List (Nat × Nat × Nat) := [(2252752896,98027174038580,98027553203645),(2252823552,98027587856811,98027967022128)]
theorem point_links_checked17157 : (cuts17157.take 2).map (fun c => (2252734465-1+2*2^9*c.k,98027065709015+c.lower,98027444874012+c.upper)) = pointBounds17157 := by
 decide +kernel
def cuts17158 : List PrefixCut := [⟨28,163796380,163796483⟩,
⟨97,572716069,572716427⟩,
⟨128,751872078,751872548⟩]
theorem checked17158 : checkPrefixCuts (2^48) 2252865537 9 Manual.Count131072.C017158.packed 128 cuts17158 = true := by
 decide +kernel
def pointBounds17158 : List (Nat × Nat × Nat) := [(2252894208,98027996539542,98028375705117),(2252964864,98028405459231,98028784625061)]
theorem point_links_checked17158 : (cuts17158.take 2).map (fun c => (2252865537-1+2*2^9*c.k,98027832743162+c.lower,98028211908634+c.upper)) = pointBounds17158 := by
 decide +kernel
def cuts17159 : List PrefixCut := [⟨38,223629148,223629284⟩,
⟨107,631773623,631774020⟩,
⟨128,758199643,758200119⟩]
theorem checked17159 : checkPrefixCuts (2^48) 2252996609 9 Manual.Count131072.C017159.packed 128 cuts17159 = true := by
 decide +kernel
def pointBounds17159 : List (Nat × Nat × Nat) := [(2253035520,98028808244388,98029187410466),(2253106176,98029216388863,98029595555202)]
theorem point_links_checked17159 : (cuts17159.take 2).map (fun c => (2252996609-1+2*2^9*c.k,98028584615240+c.lower,98028963781182+c.upper)) = pointBounds17159 := by
 decide +kernel
def cuts17160 : List PrefixCut := [⟨48,287702172,287702351⟩,
⟨117,699818624,699819060⟩,
⟨128,765151438,765151914⟩]
theorem checked17160 : checkPrefixCuts (2^48) 2253127681 9 Manual.Count131072.C017160.packed 128 cuts17160 = true := by
 decide +kernel
def pointBounds17160 : List (Nat × Nat × Nat) := [(2253176832,98029630517055,98030009683652),(2253247488,98030042633507,98030421800361)]
theorem point_links_checked17160 : (cuts17160.take 2).map (fun c => (2253127681-1+2*2^9*c.k,98029342814883+c.lower,98029721981301+c.upper)) = pointBounds17160 := by
 decide +kernel
def cuts17161 : List PrefixCut := [⟨58,342273551,342273771⟩,
⟨127,746494526,746495000⟩,
⟨128,751990645,751991122⟩]
theorem checked17161 : checkPrefixCuts (2^48) 2253258753 9 Manual.Count131072.C017161.packed 128 cuts17161 = true := by
 decide +kernel
def pointBounds17161 : List (Nat × Nat × Nat) := [(2253318144,98030450239872,98030829406986),(2253388800,98030854460847,98031233628215)]
theorem point_links_checked17161 : (cuts17161.take 2).map (fun c => (2253258753-1+2*2^9*c.k,98030107966321+c.lower,98030487133215+c.upper)) = pointBounds17161 := by
 decide +kernel
def cuts17162 : List PrefixCut := [⟨68,409079720,409079975⟩,
⟨128,765312225,765312700⟩]
theorem checked17162 : checkPrefixCuts (2^48) 2253389825 9 Manual.Count131072.C017162.packed 128 cuts17162 = true := by
 decide +kernel
def pointBounds17162 : List (Nat × Nat × Nat) := [(2253459456,98031269036686,98031648204312)]
theorem point_links_checked17162 : (cuts17162.take 1).map (fun c => (2253389825-1+2*2^9*c.k,98030859956966+c.lower,98031239124337+c.upper)) = pointBounds17162 := by
 decide +kernel
def cuts17163 : List PrefixCut := [⟨9,52459776,52459809⟩,
⟨78,455268808,455269095⟩,
⟨128,755400238,755400709⟩]
theorem checked17163 : checkPrefixCuts (2^48) 2253520897 9 Manual.Count131072.C017163.packed 128 cuts17163 = true := by
 decide +kernel
def pointBounds17163 : List (Nat × Nat × Nat) := [(2253530112,98031677728967,98032056896846),(2253600768,98032080537999,98032459706132)]
theorem point_links_checked17163 : (cuts17163.take 2).map (fun c => (2253520897-1+2*2^9*c.k,98031625269191+c.lower,98032004437037+c.upper)) = pointBounds17163 := by
 decide +kernel
def cuts17164 : List PrefixCut := [⟨19,110908256,110908323⟩,
⟨88,528054941,528055264⟩,
⟨128,762475569,762476038⟩]
theorem checked17164 : checkPrefixCuts (2^48) 2253651969 9 Manual.Count131072.C017164.packed 128 cuts17164 = true := by
 decide +kernel
def pointBounds17164 : List (Nat × Nat × Nat) := [(2253671424,98032491577685,98032870746069),(2253742080,98032908724370,98033287893010)]
theorem point_links_checked17164 : (cuts17164.take 2).map (fun c => (2253651969-1+2*2^9*c.k,98032380669429+c.lower,98032759837746+c.upper)) = pointBounds17164 := by
 decide +kernel
def cuts17165 : List PrefixCut := [⟨29,173595912,173596018⟩,
⟨98,572607929,572608280⟩,
⟨128,751316313,751316777⟩]
theorem checked17165 : checkPrefixCuts (2^48) 2253783041 9 Manual.Count131072.C017165.packed 128 cuts17165 = true := by
 decide +kernel
def pointBounds17165 : List (Nat × Nat × Nat) := [(2253812736,98033316740910,98033695909802),(2253883392,98033715752927,98034094922064)]
theorem point_links_checked17165 : (cuts17165.take 2).map (fun c => (2253783041-1+2*2^9*c.k,98033143144998+c.lower,98033522313784+c.upper)) = pointBounds17165 := by
 decide +kernel
def cuts17166 : List PrefixCut := [⟨39,235901316,235901463⟩,
⟨108,640632613,640633016⟩,
⟨128,761013090,761013567⟩]
theorem checked17166 : checkPrefixCuts (2^48) 2253914113 9 Manual.Count131072.C017166.packed 128 cuts17166 = true := by
 decide +kernel
def pointBounds17166 : List (Nat × Nat × Nat) := [(2253954048,98034130362627,98034509532024),(2254024704,98034535093924,98034914263577)]
theorem point_links_checked17166 : (cuts17166.take 2).map (fun c => (2253914113-1+2*2^9*c.k,98033894461311+c.lower,98034273630561+c.upper)) = pointBounds17166 := by
 decide +kernel
def cuts17167 : List PrefixCut := [⟨49,291580903,291581086⟩,
⟨118,698909175,698909614⟩,
⟨128,754225907,754226380⟩]
theorem checked17167 : checkPrefixCuts (2^48) 2254045185 9 Manual.Count131072.C017167.packed 128 cuts17167 = true := by
 decide +kernel
def pointBounds17167 : List (Nat × Nat × Nat) := [(2254095360,98034947055304,98035326225214),(2254166016,98035354383576,98035733553742)]
theorem point_links_checked17167 : (cuts17167.take 2).map (fun c => (2254045185-1+2*2^9*c.k,98034655474401+c.lower,98035034644128+c.upper)) = pointBounds17167 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000223
