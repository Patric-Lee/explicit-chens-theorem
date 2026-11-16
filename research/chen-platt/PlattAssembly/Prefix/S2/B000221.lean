import PlattAssemblyKernel
import PlattCertificates.Count131072.C017072
import PlattCertificates.Count131072.C017073
import PlattCertificates.Count131072.C017074
import PlattCertificates.Count131072.C017075
import PlattCertificates.Count131072.C017076
import PlattCertificates.Count131072.C017077
import PlattCertificates.Count131072.C017078
import PlattCertificates.Count131072.C017079
import PlattCertificates.Count131072.C017080
import PlattCertificates.Count131072.C017081
import PlattCertificates.Count131072.C017082
import PlattCertificates.Count131072.C017083
import PlattCertificates.Count131072.C017084
import PlattCertificates.Count131072.C017085
import PlattCertificates.Count131072.C017086
import PlattCertificates.Count131072.C017087
import PlattCertificates.Count131072.C017088
import PlattCertificates.Count131072.C017089
import PlattCertificates.Count131072.C017090
import PlattCertificates.Count131072.C017091
import PlattCertificates.Count131072.C017092
import PlattCertificates.Count131072.C017093
import PlattCertificates.Count131072.C017094
import PlattCertificates.Count131072.C017095
import PlattCertificates.Count131072.C017096
import PlattCertificates.Count131072.C017097
import PlattCertificates.Count131072.C017098
import PlattCertificates.Count131072.C017099
import PlattCertificates.Count131072.C017100
import PlattCertificates.Count131072.C017101
import PlattCertificates.Count131072.C017102
import PlattCertificates.Count131072.C017103
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000221
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts17072 : List PrefixCut := [⟨65,383356764,383357009⟩,
⟨128,763814437,763814921⟩]
theorem checked17072 : checkPrefixCuts (2^48) 2241593345 9 Manual.Count131072.C017072.packed 128 cuts17072 = true := by
 decide +kernel
def pointBounds17072 : List (Nat × Nat × Nat) := [(2241659904,97962616177899,97962995302712)]
theorem point_links_checked17072 : (cuts17072.take 1).map (fun c => (2241593345-1+2*2^9*c.k,97962232821135+c.lower,97962611945703+c.upper)) = pointBounds17072 := by
 decide +kernel
def cuts17073 : List PrefixCut := [⟨6,35031684,35031706⟩,
⟨75,446113311,446113588⟩,
⟨128,762765385,762765862⟩]
theorem checked17073 : checkPrefixCuts (2^48) 2241724417 9 Manual.Count131072.C017073.packed 128 cuts17073 = true := by
 decide +kernel
def pointBounds17073 : List (Nat × Nat × Nat) := [(2241730560,97963031667256,97963410792330),(2241801216,97963442748883,97963821874212)]
theorem point_links_checked17073 : (cuts17073.take 2).map (fun c => (2241724417-1+2*2^9*c.k,97962996635572+c.lower,97963375760624+c.upper)) = pointBounds17073 := by
 decide +kernel
def cuts17074 : List PrefixCut := [⟨16,91654397,91654454⟩,
⟨85,492666014,492666324⟩,
⟨128,744139316,744139779⟩]
theorem checked17074 : checkPrefixCuts (2^48) 2241855489 9 Manual.Count131072.C017074.packed 128 cuts17074 = true := by
 decide +kernel
def pointBounds17074 : List (Nat × Nat × Nat) := [(2241871872,97963851055354,97964230180940),(2241942528,97964252066971,97964631192810)]
theorem point_links_checked17074 : (cuts17074.take 2).map (fun c => (2241855489-1+2*2^9*c.k,97963759400957+c.lower,97964138526486+c.upper)) = pointBounds17074 := by
 decide +kernel
def cuts17075 : List PrefixCut := [⟨26,149902335,149902427⟩,
⟨95,567586011,567586359⟩,
⟨128,759663277,759663740⟩]
theorem checked17075 : checkPrefixCuts (2^48) 2241986561 9 Manual.Count131072.C017075.packed 128 cuts17075 = true := by
 decide +kernel
def pointBounds17075 : List (Nat × Nat × Nat) := [(2242013184,97964653442608,97965032568692),(2242083840,97965071126284,97965450252624)]
theorem point_links_checked17075 : (cuts17075.take 2).map (fun c => (2241986561-1+2*2^9*c.k,97964503540273+c.lower,97964882666265+c.upper)) = pointBounds17075 := by
 decide +kernel
def cuts17076 : List PrefixCut := [⟨36,214420141,214420278⟩,
⟨105,628436936,628437328⟩,
⟨128,763385002,763385476⟩]
theorem checked17076 : checkPrefixCuts (2^48) 2242117633 9 Manual.Count131072.C017076.packed 128 cuts17076 = true := by
 decide +kernel
def pointBounds17076 : List (Nat × Nat × Nat) := [(2242154496,97965477623691,97965856750283),(2242225152,97965891640486,97966270767333)]
theorem point_links_checked17076 : (cuts17076.take 2).map (fun c => (2242117633-1+2*2^9*c.k,97965263203550+c.lower,97965642330005+c.upper)) = pointBounds17076 := by
 decide +kernel
def cuts17077 : List PrefixCut := [⟨46,273281195,273281363⟩,
⟨115,684008160,684008582⟩,
⟨128,762587098,762587568⟩]
theorem checked17077 : checkPrefixCuts (2^48) 2242248705 9 Manual.Count131072.C017077.packed 128 cuts17077 = true := by
 decide +kernel
def pointBounds17077 : List (Nat × Nat × Nat) := [(2242295808,97966299869747,97966678996844),(2242366464,97966710596712,97967089724063)]
theorem point_links_checked17077 : (cuts17077.take 2).map (fun c => (2242248705-1+2*2^9*c.k,97966026588552+c.lower,97966405715481+c.upper)) = pointBounds17077 := by
 decide +kernel
def cuts17078 : List PrefixCut := [⟨56,338662297,338662506⟩,
⟨125,757271122,757271596⟩,
⟨128,774843618,774844103⟩]
theorem checked17078 : checkPrefixCuts (2^48) 2242379777 9 Manual.Count131072.C017078.packed 128 cuts17078 = true := by
 decide +kernel
def pointBounds17078 : List (Nat × Nat × Nat) := [(2242437120,97967127837947,97967506965555),(2242507776,97967546446772,97967925574645)]
theorem point_links_checked17078 : (cuts17078.take 2).map (fun c => (2242379777-1+2*2^9*c.k,97966789175650+c.lower,97967168303049+c.upper)) = pointBounds17078 := by
 decide +kernel
def cuts17079 : List PrefixCut := [⟨66,400395501,400395753⟩,
⟨128,771534939,771535421⟩]
theorem checked17079 : checkPrefixCuts (2^48) 2242510849 9 Manual.Count131072.C017079.packed 128 cuts17079 = true := by
 decide +kernel
def pointBounds17079 : List (Nat × Nat × Nat) := [(2242578432,97967964414769,97968343542905)]
theorem point_links_checked17079 : (cuts17079.take 1).map (fun c => (2242510849-1+2*2^9*c.k,97967564019268+c.lower,97967943147152+c.upper)) = pointBounds17079 := by
 decide +kernel
def cuts17080 : List PrefixCut := [⟨7,40665304,40665330⟩,
⟨76,448064278,448064557⟩,
⟨128,757558417,757558886⟩]
theorem checked17080 : checkPrefixCuts (2^48) 2242641921 9 Manual.Count131072.C017080.packed 128 cuts17080 = true := by
 decide +kernel
def pointBounds17080 : List (Nat × Nat × Nat) := [(2242649088,97968376219511,97968755347903),(2242719744,97968783618485,97969162747130)]
theorem point_links_checked17080 : (cuts17080.take 2).map (fun c => (2242641921-1+2*2^9*c.k,97968335554207+c.lower,97968714682573+c.upper)) = pointBounds17080 := by
 decide +kernel
def cuts17081 : List PrefixCut := [⟨17,96134972,96135032⟩,
⟨86,509657817,509658139⟩,
⟨128,760651698,760652179⟩]
theorem checked17081 : checkPrefixCuts (2^48) 2242772993 9 Manual.Count131072.C017081.packed 128 cuts17081 = true := by
 decide +kernel
def pointBounds17081 : List (Nat × Nat × Nat) := [(2242790400,97969189247596,97969568376491),(2242861056,97969602770441,97969981899598)]
theorem point_links_checked17081 : (cuts17081.take 2).map (fun c => (2242772993-1+2*2^9*c.k,97969093112624+c.lower,97969472241459+c.upper)) = pointBounds17081 := by
 decide +kernel
def cuts17082 : List PrefixCut := [⟨27,162892452,162892553⟩,
⟨96,570240175,570240534⟩,
⟨128,762740783,762741262⟩]
theorem checked17082 : checkPrefixCuts (2^48) 2242904065 9 Manual.Count131072.C017082.packed 128 cuts17082 = true := by
 decide +kernel
def pointBounds17082 : List (Nat × Nat × Nat) := [(2242931712,97970016656774,97970395786191),(2243002368,97970424004497,97970803134172)]
theorem point_links_checked17082 : (cuts17082.take 2).map (fun c => (2242904065-1+2*2^9*c.k,97969853764322+c.lower,97970232893638+c.upper)) = pointBounds17082 := by
 decide +kernel
def cuts17083 : List PrefixCut := [⟨37,221736119,221736258⟩,
⟨106,628054282,628054675⟩,
⟨128,761817767,761818243⟩]
theorem checked17083 : checkPrefixCuts (2^48) 2243035137 9 Manual.Count131072.C017083.packed 128 cuts17083 = true := by
 decide +kernel
def pointBounds17083 : List (Nat × Nat × Nat) := [(2243073024,97970838241224,97971217371158),(2243143680,97971244559387,97971623689575)]
theorem point_links_checked17083 : (cuts17083.take 2).map (fun c => (2243035137-1+2*2^9*c.k,97970616505105+c.lower,97970995634900+c.upper)) = pointBounds17083 := by
 decide +kernel
def cuts17084 : List PrefixCut := [⟨47,278564982,278565153⟩,
⟨116,690002028,690002450⟩,
⟨128,760016556,760017022⟩]
theorem checked17084 : checkPrefixCuts (2^48) 2243166209 9 Manual.Count131072.C017084.packed 128 cuts17084 = true := by
 decide +kernel
def pointBounds17084 : List (Nat × Nat × Nat) := [(2243214336,97971656887854,97972036018296),(2243284992,97972068324900,97972447455593)]
theorem point_links_checked17084 : (cuts17084.take 2).map (fun c => (2243166209-1+2*2^9*c.k,97971378322872+c.lower,97971757453143+c.upper)) = pointBounds17084 := by
 decide +kernel
def cuts17085 : List PrefixCut := [⟨57,334759528,334759739⟩,
⟨126,739646398,739646868⟩,
⟨128,753573176,753573654⟩]
theorem checked17085 : checkPrefixCuts (2^48) 2243297281 9 Manual.Count131072.C017085.packed 128 cuts17085 = true := by
 decide +kernel
def pointBounds17085 : List (Nat × Nat × Nat) := [(2243355648,97972473098956,97972852229904),(2243426304,97972877985826,97973257117033)]
theorem point_links_checked17085 : (cuts17085.take 2).map (fun c => (2243297281-1+2*2^9*c.k,97972138339428+c.lower,97972517470165+c.upper)) = pointBounds17085 := by
 decide +kernel
def cuts17086 : List PrefixCut := [⟨67,410770810,410771064⟩,
⟨128,776238164,776238642⟩]
theorem checked17086 : checkPrefixCuts (2^48) 2243428353 9 Manual.Count131072.C017086.packed 128 cuts17086 = true := by
 decide +kernel
def pointBounds17086 : List (Nat × Nat × Nat) := [(2243496960,97973302683414,97973681814883)]
theorem point_links_checked17086 : (cuts17086.take 1).map (fun c => (2243428353-1+2*2^9*c.k,97972891912604+c.lower,97973271043819+c.upper)) = pointBounds17086 := by
 decide +kernel
def cuts17087 : List PrefixCut := [⟨8,47423441,47423471⟩,
⟨77,446751946,446752226⟩,
⟨128,749219580,749220050⟩]
theorem checked17087 : checkPrefixCuts (2^48) 2243559425 9 Manual.Count131072.C017087.packed 128 cuts17087 = true := by
 decide +kernel
def pointBounds17087 : List (Nat × Nat × Nat) := [(2243567616,97973715574209,97974094705932),(2243638272,97974114902714,97974494034687)]
theorem point_links_checked17087 : (cuts17087.take 2).map (fun c => (2243559425-1+2*2^9*c.k,97973668150768+c.lower,97974047282461+c.upper)) = pointBounds17087 := by
 decide +kernel
def cuts17088 : List PrefixCut := [⟨18,104626324,104626392⟩,
⟨87,517728983,517729312⟩,
⟨128,769247404,769247890⟩]
theorem checked17088 : checkPrefixCuts (2^48) 2243690497 9 Manual.Count131072.C017088.packed 128 cuts17088 = true := by
 decide +kernel
def pointBounds17088 : List (Nat × Nat × Nat) := [(2243708928,97974521996672,97974901128903),(2243779584,97974935099331,97975314231823)]
theorem point_links_checked17088 : (cuts17088.take 2).map (fun c => (2243690497-1+2*2^9*c.k,97974417370348+c.lower,97974796502511+c.upper)) = pointBounds17088 := by
 decide +kernel
def cuts17089 : List PrefixCut := [⟨28,172861306,172861411⟩,
⟨97,580418533,580418892⟩,
⟨128,770833380,770833856⟩]
theorem checked17089 : checkPrefixCuts (2^48) 2243821569 9 Manual.Count131072.C017089.packed 128 cuts17089 = true := by
 decide +kernel
def pointBounds17089 : List (Nat × Nat × Nat) := [(2243850240,97975359479058,97975738611812),(2243920896,97975767036285,97976146169293)]
theorem point_links_checked17089 : (cuts17089.take 2).map (fun c => (2243821569-1+2*2^9*c.k,97975186617752+c.lower,97975565750401+c.upper)) = pointBounds17089 := by
 decide +kernel
def cuts17090 : List PrefixCut := [⟨38,223652384,223652527⟩,
⟨107,638082688,638083087⟩,
⟨128,764014765,764015245⟩]
theorem checked17090 : checkPrefixCuts (2^48) 2243952641 9 Manual.Count131072.C017090.packed 128 cuts17090 = true := by
 decide +kernel
def pointBounds17090 : List (Nat × Nat × Nat) := [(2243991552,97976181103516,97976560236784),(2244062208,97976595533820,97976974667344)]
theorem point_links_checked17090 : (cuts17090.take 2).map (fun c => (2243952641-1+2*2^9*c.k,97975957451132+c.lower,97976336584257+c.upper)) = pointBounds17090 := by
 decide +kernel
def cuts17091 : List PrefixCut := [⟨48,285349604,285349784⟩,
⟨117,697998020,697998457⟩,
⟨128,766353420,766353899⟩]
theorem checked17091 : checkPrefixCuts (2^48) 2244083713 9 Manual.Count131072.C017091.packed 128 cuts17091 = true := by
 decide +kernel
def pointBounds17091 : List (Nat × Nat × Nat) := [(2244132864,97977006815501,97977385949286),(2244203520,97977419463917,97977798597959)]
theorem point_links_checked17091 : (cuts17091.take 2).map (fun c => (2244083713-1+2*2^9*c.k,97976721465897+c.lower,97977100599502+c.upper)) = pointBounds17091 := by
 decide +kernel
def cuts17092 : List PrefixCut := [⟨58,345283383,345283596⟩,
⟨127,755522885,755523356⟩,
⟨128,761291981,761292456⟩]
theorem checked17092 : checkPrefixCuts (2^48) 2244214785 9 Manual.Count131072.C017092.packed 128 cuts17092 = true := by
 decide +kernel
def pointBounds17092 : List (Nat × Nat × Nat) := [(2244274176,97977833102700,97978212236997),(2244344832,97978243342202,97978622476757)]
theorem point_links_checked17092 : (cuts17092.take 2).map (fun c => (2244214785-1+2*2^9*c.k,97977487819317+c.lower,97977866953401+c.upper)) = pointBounds17092 := by
 decide +kernel
def cuts17093 : List PrefixCut := [⟨68,403579544,403579791⟩,
⟨128,763003211,763003683⟩]
theorem checked17093 : checkPrefixCuts (2^48) 2244345857 9 Manual.Count131072.C017093.packed 128 cuts17093 = true := by
 decide +kernel
def pointBounds17093 : List (Nat × Nat × Nat) := [(2244415488,97978652690842,97979031825648)]
theorem point_links_checked17093 : (cuts17093.take 1).map (fun c => (2244345857-1+2*2^9*c.k,97978249111298+c.lower,97978628245857+c.upper)) = pointBounds17093 := by
 decide +kernel
def cuts17094 : List PrefixCut := [⟨9,54050644,54050677⟩,
⟨78,453968074,453968362⟩,
⟨128,755685024,755685499⟩]
theorem checked17094 : checkPrefixCuts (2^48) 2244476929 9 Manual.Count131072.C017094.packed 128 cuts17094 = true := by
 decide +kernel
def pointBounds17094 : List (Nat × Nat × Nat) := [(2244486144,97979066165153,97979445300217),(2244556800,97979466082583,97979845217902)]
theorem point_links_checked17094 : (cuts17094.take 2).map (fun c => (2244476929-1+2*2^9*c.k,97979012114509+c.lower,97979391249540+c.upper)) = pointBounds17094 := by
 decide +kernel
def cuts17095 : List PrefixCut := [⟨19,111229736,111229807⟩,
⟨88,529680905,529681236⟩,
⟨128,769434833,769435314⟩]
theorem checked17095 : checkPrefixCuts (2^48) 2244608001 9 Manual.Count131072.C017095.packed 128 cuts17095 = true := by
 decide +kernel
def pointBounds17095 : List (Nat × Nat × Nat) := [(2244627456,97979879029269,97980258164846),(2244698112,97980297480438,97980676616275)]
theorem point_links_checked17095 : (cuts17095.take 2).map (fun c => (2244608001-1+2*2^9*c.k,97979767799533+c.lower,97980146935039+c.upper)) = pointBounds17095 := by
 decide +kernel
def cuts17096 : List PrefixCut := [⟨29,175047677,175047784⟩,
⟨98,583817459,583817817⟩,
⟨128,765126606,765127074⟩]
theorem checked17096 : checkPrefixCuts (2^48) 2244739073 9 Manual.Count131072.C017096.packed 128 cuts17096 = true := by
 decide +kernel
def pointBounds17096 : List (Nat × Nat × Nat) := [(2244768768,97980712282043,97981091418137),(2244839424,97981121051825,97981500188170)]
theorem point_links_checked17096 : (cuts17096.take 2).map (fun c => (2244739073-1+2*2^9*c.k,97980537234366+c.lower,97980916370353+c.upper)) = pointBounds17096 := by
 decide +kernel
def cuts17097 : List PrefixCut := [⟨39,229579403,229579548⟩,
⟨108,636818805,636819206⟩,
⟨128,757684229,757684706⟩]
theorem checked17097 : checkPrefixCuts (2^48) 2244870145 9 Manual.Count131072.C017097.packed 128 cuts17097 = true := by
 decide +kernel
def pointBounds17097 : List (Nat × Nat × Nat) := [(2244910080,97981531940375,97981911076975),(2244980736,97981939179777,97982318316633)]
theorem point_links_checked17097 : (cuts17097.take 2).map (fun c => (2244870145-1+2*2^9*c.k,97981302360972+c.lower,97981681497427+c.upper)) = pointBounds17097 := by
 decide +kernel
def cuts17098 : List PrefixCut := [⟨49,298773666,298773850⟩,
⟨118,707868141,707868576⟩,
⟨128,769049423,769049895⟩]
theorem checked17098 : checkPrefixCuts (2^48) 2245001217 9 Manual.Count131072.C017098.packed 128 cuts17098 = true := by
 decide +kernel
def pointBounds17098 : List (Nat × Nat × Nat) := [(2245051392,97982358818867,97982737955983),(2245122048,97982767913342,97983147050709)]
theorem point_links_checked17098 : (cuts17098.take 2).map (fun c => (2245001217-1+2*2^9*c.k,97982060045201+c.lower,97982439182133+c.upper)) = pointBounds17098 := by
 decide +kernel
def cuts17099 : List PrefixCut := [⟨59,353541935,353542158⟩,
⟨128,763237502,763237985⟩]
theorem checked17099 : checkPrefixCuts (2^48) 2245132289 9 Manual.Count131072.C017099.packed 128 cuts17099 = true := by
 decide +kernel
def pointBounds17099 : List (Nat × Nat × Nat) := [(2245192704,97983182636559,97983561774186),(2245263360,97983592332126,97983971470013)]
theorem point_links_checked17099 : (cuts17099.take 2).map (fun c => (2245132289-1+2*2^9*c.k,97982829094624+c.lower,97983208232028+c.upper)) = pointBounds17099 := by
 decide +kernel
def cuts17100 : List PrefixCut := [⟨69,413694221,413694484⟩,
⟨128,767580540,767581021⟩]
theorem checked17100 : checkPrefixCuts (2^48) 2245263361 9 Manual.Count131072.C017100.packed 128 cuts17100 = true := by
 decide +kernel
def pointBounds17100 : List (Nat × Nat × Nat) := [(2245334016,97984006026347,97984385164497)]
theorem point_links_checked17100 : (cuts17100.take 1).map (fun c => (2245263361-1+2*2^9*c.k,97983592332126+c.lower,97983971470013+c.upper)) = pointBounds17100 := by
 decide +kernel
def cuts17101 : List PrefixCut := [⟨10,60045647,60045685⟩,
⟨79,468448967,468449265⟩,
⟨128,763524333,763524815⟩]
theorem checked17101 : checkPrefixCuts (2^48) 2245394433 9 Manual.Count131072.C017101.packed 128 cuts17101 = true := by
 decide +kernel
def pointBounds17101 : List (Nat × Nat × Nat) := [(2245404672,97984419958313,97984799096719),(2245475328,97984828361633,97985207500299)]
theorem point_links_checked17101 : (cuts17101.take 2).map (fun c => (2245394433-1+2*2^9*c.k,97984359912666+c.lower,97984739051034+c.upper)) = pointBounds17101 := by
 decide +kernel
def cuts17102 : List PrefixCut := [⟨20,117577049,117577118⟩,
⟨89,528336199,528336522⟩,
⟨128,765861220,765861690⟩]
theorem checked17102 : checkPrefixCuts (2^48) 2245525505 9 Manual.Count131072.C017102.packed 128 cuts17102 = true := by
 decide +kernel
def pointBounds17102 : List (Nat × Nat × Nat) := [(2245545984,97985241014048,97985620152967),(2245616640,97985651773198,97986030912371)]
theorem point_links_checked17102 : (cuts17102.take 2).map (fun c => (2245525505-1+2*2^9*c.k,97985123436999+c.lower,97985502575849+c.upper)) = pointBounds17102 := by
 decide +kernel
def cuts17103 : List PrefixCut := [⟨30,178485672,178485782⟩,
⟨99,588968393,588968760⟩,
⟨128,757168528,757168998⟩]
theorem checked17103 : checkPrefixCuts (2^48) 2245656577 9 Manual.Count131072.C017103.packed 128 cuts17103 = true := by
 decide +kernel
def pointBounds17103 : List (Nat × Nat × Nat) := [(2245687296,97986067783891,97986446923321),(2245757952,97986478266612,97986857406299)]
theorem point_links_checked17103 : (cuts17103.take 2).map (fun c => (2245656577-1+2*2^9*c.k,97985889298219+c.lower,97986268437539+c.upper)) = pointBounds17103 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000221
