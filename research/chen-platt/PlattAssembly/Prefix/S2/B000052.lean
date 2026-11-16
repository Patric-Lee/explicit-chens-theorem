import PlattAssemblyKernel
import PlattCertificates.Count131072.C011664
import PlattCertificates.Count131072.C011665
import PlattCertificates.Count131072.C011666
import PlattCertificates.Count131072.C011667
import PlattCertificates.Count131072.C011668
import PlattCertificates.Count131072.C011669
import PlattCertificates.Count131072.C011670
import PlattCertificates.Count131072.C011671
import PlattCertificates.Count131072.C011672
import PlattCertificates.Count131072.C011673
import PlattCertificates.Count131072.C011674
import PlattCertificates.Count131072.C011675
import PlattCertificates.Count131072.C011676
import PlattCertificates.Count131072.C011677
import PlattCertificates.Count131072.C011678
import PlattCertificates.Count131072.C011679
import PlattCertificates.Count131072.C011680
import PlattCertificates.Count131072.C011681
import PlattCertificates.Count131072.C011682
import PlattCertificates.Count131072.C011683
import PlattCertificates.Count131072.C011684
import PlattCertificates.Count131072.C011685
import PlattCertificates.Count131072.C011686
import PlattCertificates.Count131072.C011687
import PlattCertificates.Count131072.C011688
import PlattCertificates.Count131072.C011689
import PlattCertificates.Count131072.C011690
import PlattCertificates.Count131072.C011691
import PlattCertificates.Count131072.C011692
import PlattCertificates.Count131072.C011693
import PlattCertificates.Count131072.C011694
import PlattCertificates.Count131072.C011695
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000052
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts11664 : List PrefixCut := [⟨3,28096847,28096869⟩,
⟨50,442748039,442748389⟩,
⟨97,865282253,865282930⟩,
⟨128,1142006495,1142007386⟩]
theorem checked11664 : checkPrefixCuts (2^48) 1532755969 9 Manual.Count131072.C011664.packed 128 cuts11664 = true := by
 decide +kernel
def pointBounds11664 : List (Nat × Nat × Nat) := [(1532759040,92948652806405,92949028451227),(1532807168,92949067457597,92949443102747),(1532855296,92949489991811,92949865637288)]
theorem point_links_checked11664 : (cuts11664.take 3).map (fun c => (1532755969-1+2*2^9*c.k,92948624709558+c.lower,92949000354358+c.upper)) = pointBounds11664 := by
 decide +kernel
def cuts11665 : List PrefixCut := [⟨16,140838862,140838974⟩,
⟨63,558572528,558572964⟩,
⟨110,978312702,978313460⟩,
⟨128,1139705373,1139706254⟩]
theorem checked11665 : checkPrefixCuts (2^48) 1532887041 9 Manual.Count131072.C011665.packed 128 cuts11665 = true := by
 decide +kernel
def pointBounds11665 : List (Nat × Nat × Nat) := [(1532903424,92949907554915,92950283200718),(1532951552,92950325288581,92950700934708),(1532999680,92950745028755,92951120675204)]
theorem point_links_checked11665 : (cuts11665.take 3).map (fun c => (1532887041-1+2*2^9*c.k,92949766716053+c.lower,92950142361744+c.upper)) = pointBounds11665 := by
 decide +kernel
def cuts11666 : List PrefixCut := [⟨29,258150784,258150987⟩,
⟨76,667766499,667767027⟩,
⟨123,1084162442,1084163298⟩,
⟨128,1128959115,1128960006⟩]
theorem checked11666 : checkPrefixCuts (2^48) 1533018113 9 Manual.Count131072.C011666.packed 128 cuts11666 = true := by
 decide +kernel
def pointBounds11666 : List (Nat × Nat × Nat) := [(1533047808,92951164572210,92951540218985),(1533095936,92951574187925,92951949835025),(1533144064,92951990583868,92952366231296)]
theorem point_links_checked11666 : (cuts11666.take 3).map (fun c => (1533018113-1+2*2^9*c.k,92950906421426+c.lower,92951282067998+c.upper)) = pointBounds11666 := by
 decide +kernel
def cuts11667 : List PrefixCut := [⟨42,376726723,376727016⟩,
⟨89,795299620,795300237⟩,
⟨128,1138409320,1138410203⟩]
theorem checked11667 : checkPrefixCuts (2^48) 1533149185 9 Manual.Count131072.C011667.packed 128 cuts11667 = true := by
 decide +kernel
def pointBounds11667 : List (Nat × Nat × Nat) := [(1533192192,92952412107264,92952787755020),(1533240320,92952830680161,92953206328241)]
theorem point_links_checked11667 : (cuts11667.take 2).map (fun c => (1533149185-1+2*2^9*c.k,92952035380541+c.lower,92952411028004+c.upper)) = pointBounds11667 := by
 decide +kernel
def cuts11668 : List PrefixCut := [⟨8,69942619,69942673⟩,
⟨55,484817709,484818086⟩,
⟨102,901699090,901699792⟩,
⟨128,1134456766,1134457651⟩]
theorem checked11668 : checkPrefixCuts (2^48) 1533280257 9 Manual.Count131072.C011668.packed 128 cuts11668 = true := by
 decide +kernel
def pointBounds11668 : List (Nat × Nat × Nat) := [(1533288448,92953243732480,92953619380880),(1533336576,92953658607570,92954034256293),(1533384704,92954075488951,92954451137999)]
theorem point_links_checked11668 : (cuts11668.take 3).map (fun c => (1533280257-1+2*2^9*c.k,92953173789861+c.lower,92953549438207+c.upper)) = pointBounds11668 := by
 decide +kernel
def cuts11669 : List PrefixCut := [⟨21,189066738,189066886⟩,
⟨68,605187596,605188076⟩,
⟨115,1016523204,1016524011⟩,
⟨128,1129220668,1129221564⟩]
theorem checked11669 : checkPrefixCuts (2^48) 1533411329 9 Manual.Count131072.C011669.packed 128 cuts11669 = true := by
 decide +kernel
def pointBounds11669 : List (Nat × Nat × Nat) := [(1533432832,92954497313365,92954872962744),(1533480960,92954913434223,92955289083934),(1533529088,92955324769831,92955700419869)]
theorem point_links_checked11669 : (cuts11669.take 3).map (fun c => (1533411329-1+2*2^9*c.k,92954308246627+c.lower,92954683895858+c.upper)) = pointBounds11669 := by
 decide +kernel
def cuts11670 : List PrefixCut := [⟨34,309454273,309454512⟩,
⟨81,725719591,725720160⟩,
⟨128,1148211976,1148212873⟩]
theorem checked11670 : checkPrefixCuts (2^48) 1533542401 9 Manual.Count131072.C011670.packed 128 cuts11670 = true := by
 decide +kernel
def pointBounds11670 : List (Nat × Nat × Nat) := [(1533577216,92955746921568,92956122571934),(1533625344,92956163186886,92956538837582),(1533673472,92956585679271,92956961330295)]
theorem point_links_checked11670 : (cuts11670.take 3).map (fun c => (1533542401-1+2*2^9*c.k,92955437467295+c.lower,92955813117422+c.upper)) = pointBounds11670 := by
 decide +kernel
def cuts11671 : List PrefixCut := [⟨47,426149632,426149962⟩,
⟨94,838888742,838889395⟩,
⟨128,1142791650,1142792535⟩]
theorem checked11671 : checkPrefixCuts (2^48) 1533673473 9 Manual.Count131072.C011671.packed 128 cuts11671 = true := by
 decide +kernel
def pointBounds11671 : List (Nat × Nat × Nat) := [(1533721600,92957011828903,92957387480257),(1533769728,92957424568013,92957800219690)]
theorem point_links_checked11671 : (cuts11671.take 2).map (fun c => (1533673473-1+2*2^9*c.k,92956585679271+c.lower,92956961330295+c.upper)) = pointBounds11671 := by
 decide +kernel
def cuts11672 : List PrefixCut := [⟨13,120935309,120935402⟩,
⟨60,544475585,544476008⟩,
⟨107,961029543,961030285⟩,
⟨128,1148566311,1148567198⟩]
theorem checked11672 : checkPrefixCuts (2^48) 1533804545 9 Manual.Count131072.C011672.packed 128 cuts11672 = true := by
 decide +kernel
def pointBounds11672 : List (Nat × Nat × Nat) := [(1533817856,92957849406230,92958225058232),(1533865984,92958272946506,92958648598838),(1533914112,92958689500464,92959065153115)]
theorem point_links_checked11672 : (cuts11672.take 3).map (fun c => (1533804545-1+2*2^9*c.k,92957728470921+c.lower,92958104122830+c.upper)) = pointBounds11672 := by
 decide +kernel
def cuts11673 : List PrefixCut := [⟨26,228820619,228820798⟩,
⟨73,647917370,647917872⟩,
⟨120,1057092576,1057093397⟩,
⟨128,1127366675,1127367550⟩]
theorem checked11673 : checkPrefixCuts (2^48) 1533935617 9 Manual.Count131072.C011673.packed 128 cuts11673 = true := by
 decide +kernel
def pointBounds11673 : List (Nat × Nat × Nat) := [(1533962240,92959105857851,92959481510826),(1534010368,92959524954602,92959900607900),(1534058496,92959934129808,92960309783425)]
theorem point_links_checked11673 : (cuts11673.take 3).map (fun c => (1533935617-1+2*2^9*c.k,92958877037232+c.lower,92959252690028+c.upper)) = pointBounds11673 := by
 decide +kernel
def cuts11674 : List PrefixCut := [⟨39,338154422,338154686⟩,
⟨86,757395130,757395723⟩,
⟨128,1132040253,1132041144⟩]
theorem checked11674 : checkPrefixCuts (2^48) 1534066689 9 Manual.Count131072.C011674.packed 128 cuts11674 = true := by
 decide +kernel
def pointBounds11674 : List (Nat × Nat × Nat) := [(1534106624,92960342558329,92960718212264),(1534154752,92960761799037,92961137453301)]
theorem point_links_checked11674 : (cuts11674.take 2).map (fun c => (1534066689-1+2*2^9*c.k,92960004403907+c.lower,92960380057578+c.upper)) = pointBounds11674 := by
 decide +kernel
def cuts11675 : List PrefixCut := [⟨5,43114705,43114739⟩,
⟨52,455724513,455724866⟩,
⟨99,865386018,865386688⟩,
⟨128,1121303291,1121304163⟩]
theorem checked11675 : checkPrefixCuts (2^48) 1534197761 9 Manual.Count131072.C011675.packed 128 cuts11675 = true := by
 decide +kernel
def pointBounds11675 : List (Nat × Nat × Nat) := [(1534202880,92961179558865,92961555213461),(1534251008,92961592168673,92961967823588),(1534299136,92962001830178,92962377485410)]
theorem point_links_checked11675 : (cuts11675.take 3).map (fun c => (1534197761-1+2*2^9*c.k,92961136444160+c.lower,92961512098722+c.upper)) = pointBounds11675 := by
 decide +kernel
def cuts11676 : List PrefixCut := [⟨18,167490197,167490328⟩,
⟨65,586848573,586849029⟩,
⟨112,1003075418,1003076201⟩,
⟨128,1139552384,1139553274⟩]
theorem checked11676 : checkPrefixCuts (2^48) 1534328833 9 Manual.Count131072.C011676.packed 128 cuts11676 = true := by
 decide +kernel
def pointBounds11676 : List (Nat × Nat × Nat) := [(1534347264,92962425237648,92962800893213),(1534395392,92962844596024,92963220251914),(1534443520,92963260822869,92963636479086)]
theorem point_links_checked11676 : (cuts11676.take 3).map (fun c => (1534328833-1+2*2^9*c.k,92962257747451+c.lower,92962633402885+c.upper)) = pointBounds11676 := by
 decide +kernel
def cuts11677 : List PrefixCut := [⟨31,288724939,288725162⟩,
⟨78,699789595,699790139⟩,
⟨125,1117444689,1117445558⟩,
⟨128,1142573272,1142574161⟩]
theorem checked11677 : checkPrefixCuts (2^48) 1534459905 9 Manual.Count131072.C011677.packed 128 cuts11677 = true := by
 decide +kernel
def pointBounds11677 : List (Nat × Nat × Nat) := [(1534491648,92963686024774,92964061681321),(1534539776,92964097089430,92964472746298),(1534587904,92964514744524,92964890401717)]
theorem point_links_checked11677 : (cuts11677.take 3).map (fun c => (1534459905-1+2*2^9*c.k,92963397299835+c.lower,92963772956159+c.upper)) = pointBounds11677 := by
 decide +kernel
def cuts11678 : List PrefixCut := [⟨44,393613755,393614061⟩,
⟨91,819129367,819130010⟩,
⟨128,1138990626,1138991519⟩]
theorem checked11678 : checkPrefixCuts (2^48) 1534590977 9 Manual.Count131072.C011678.packed 128 cuts11678 = true := by
 decide +kernel
def pointBounds11678 : List (Nat × Nat × Nat) := [(1534636032,92964933486862,92965309144381),(1534684160,92965359002474,92965734660330)]
theorem point_links_checked11678 : (cuts11678.take 2).map (fun c => (1534590977-1+2*2^9*c.k,92964539873107+c.lower,92964915530320+c.upper)) = pointBounds11678 := by
 decide +kernel
def cuts11679 : List PrefixCut := [⟨10,92435533,92435604⟩,
⟨57,508570873,508571267⟩,
⟨104,934229759,934230485⟩,
⟨128,1147145869,1147146759⟩]
theorem checked11679 : checkPrefixCuts (2^48) 1534722049 9 Manual.Count131072.C011679.packed 128 cuts11679 = true := by
 decide +kernel
def pointBounds11679 : List (Nat × Nat × Nat) := [(1534732288,92965771299266,92966146957443),(1534780416,92966187434606,92966563093106),(1534828544,92966613093492,92966988752324)]
theorem point_links_checked11679 : (cuts11679.take 3).map (fun c => (1534722049-1+2*2^9*c.k,92965678863733+c.lower,92966054521839+c.upper)) = pointBounds11679 := by
 decide +kernel
def cuts11680 : List PrefixCut := [⟨23,202276279,202276440⟩,
⟨70,619472867,619473352⟩,
⟨117,1032622078,1032622884⟩,
⟨128,1130727067,1130727951⟩]
theorem checked11680 : checkPrefixCuts (2^48) 1534853121 9 Manual.Count131072.C011680.packed 128 cuts11680 = true := by
 decide +kernel
def pointBounds11680 : List (Nat × Nat × Nat) := [(1534876672,92967028285881,92967403945038),(1534924800,92967445482469,92967821141950),(1534972928,92967858631680,92968234291482)]
theorem point_links_checked11680 : (cuts11680.take 3).map (fun c => (1534853121-1+2*2^9*c.k,92966826009602+c.lower,92967201668598+c.upper)) = pointBounds11680 := by
 decide +kernel
def cuts11681 : List PrefixCut := [⟨36,320349043,320349290⟩,
⟨83,738789949,738790524⟩,
⟨128,1137231705,1137232587⟩]
theorem checked11681 : checkPrefixCuts (2^48) 1534984193 9 Manual.Count131072.C011681.packed 128 cuts11681 = true := by
 decide +kernel
def pointBounds11681 : List (Nat × Nat × Nat) := [(1535021056,92968277085712,92968652745839),(1535069184,92968695526618,92969071187073)]
theorem point_links_checked11681 : (cuts11681.take 2).map (fun c => (1534984193-1+2*2^9*c.k,92967956736669+c.lower,92968332396549+c.upper)) = pointBounds11681 := by
 decide +kernel
def cuts11682 : List PrefixCut := [⟨2,15952091,15952104⟩,
⟨49,433266649,433266986⟩,
⟨96,852584911,852585573⟩,
⟨128,1130717454,1130718333⟩]
theorem checked11682 : checkPrefixCuts (2^48) 1535115265 9 Manual.Count131072.C011682.packed 128 cuts11682 = true := by
 decide +kernel
def pointBounds11682 : List (Nat × Nat × Nat) := [(1535117312,92969109920465,92969485581240),(1535165440,92969527235023,92969902896122),(1535213568,92969946553285,92970322214709)]
theorem point_links_checked11682 : (cuts11682.take 3).map (fun c => (1535115265-1+2*2^9*c.k,92969093968374+c.lower,92969469629136+c.upper)) = pointBounds11682 := by
 decide +kernel
def cuts11683 : List PrefixCut := [⟨15,137689016,137689122⟩,
⟨62,554414290,554414720⟩,
⟨109,972226456,972227213⟩,
⟨128,1146570742,1146571634⟩]
theorem checked11683 : checkPrefixCuts (2^48) 1535246337 9 Manual.Count131072.C011683.packed 128 cuts11683 = true := by
 decide +kernel
def pointBounds11683 : List (Nat × Nat × Nat) := [(1535261696,92970362374844,92970738036591),(1535309824,92970779100118,92971154762189),(1535357952,92971196912284,92971572574682)]
theorem point_links_checked11683 : (cuts11683.take 3).map (fun c => (1535246337-1+2*2^9*c.k,92970224685828+c.lower,92970600347469+c.upper)) = pointBounds11683 := by
 decide +kernel
def cuts11684 : List PrefixCut := [⟨28,248771295,248771492⟩,
⟨75,662340979,662341504⟩,
⟨122,1069298428,1069299272⟩,
⟨128,1124291695,1124292583⟩]
theorem checked11684 : checkPrefixCuts (2^48) 1535377409 9 Manual.Count131072.C011684.packed 128 cuts11684 = true := by
 decide +kernel
def pointBounds11684 : List (Nat × Nat × Nat) := [(1535406080,92971620027865,92971995690595),(1535454208,92972033597549,92972409260607),(1535502336,92972440554998,92972816218375)]
theorem point_links_checked11684 : (cuts11684.take 3).map (fun c => (1535377409-1+2*2^9*c.k,92971371256570+c.lower,92971746919103+c.upper)) = pointBounds11684 := by
 decide +kernel
def cuts11685 : List PrefixCut := [⟨41,360750215,360750497⟩,
⟨88,769331844,769332444⟩,
⟨128,1126944878,1126945759⟩]
theorem checked11685 : checkPrefixCuts (2^48) 1535508481 9 Manual.Count131072.C011685.packed 128 cuts11685 = true := by
 decide +kernel
def pointBounds11685 : List (Nat × Nat × Nat) := [(1535550464,92972856298480,92973231962183),(1535598592,92973264880109,92973640544130)]
theorem point_links_checked11685 : (cuts11685.take 2).map (fun c => (1535508481-1+2*2^9*c.k,92972495548265+c.lower,92972871211686+c.upper)) = pointBounds11685 := by
 decide +kernel
def cuts11686 : List PrefixCut := [⟨7,61220351,61220398⟩,
⟨54,493787446,493787828⟩,
⟨101,903796852,903797558⟩,
⟨128,1142611839,1142612734⟩]
theorem checked11686 : checkPrefixCuts (2^48) 1535639553 9 Manual.Count131072.C011686.packed 128 cuts11686 = true := by
 decide +kernel
def pointBounds11686 : List (Nat × Nat × Nat) := [(1535646720,92973683713494,92974059377843),(1535694848,92974116280589,92974491945273),(1535742976,92974526289995,92974901955003)]
theorem point_links_checked11686 : (cuts11686.take 3).map (fun c => (1535639553-1+2*2^9*c.k,92973622493143+c.lower,92973998157445+c.upper)) = pointBounds11686 := by
 decide +kernel
def cuts11687 : List PrefixCut := [⟨20,173014441,173014579⟩,
⟨67,590145912,590146372⟩,
⟨114,1015511359,1015512148⟩,
⟨128,1137198952,1137199836⟩]
theorem checked11687 : checkPrefixCuts (2^48) 1535770625 9 Manual.Count131072.C011687.packed 128 cuts11687 = true := by
 decide +kernel
def pointBounds11687 : List (Nat × Nat × Nat) := [(1535791104,92974938119423,92975313784758),(1535839232,92975355250894,92975730916551),(1535887360,92975780616341,92976156282327)]
theorem point_links_checked11687 : (cuts11687.take 3).map (fun c => (1535770625-1+2*2^9*c.k,92974765104982+c.lower,92975140770179+c.upper)) = pointBounds11687 := by
 decide +kernel
def cuts11688 : List PrefixCut := [⟨33,292668743,292668971⟩,
⟨80,709394440,709394991⟩,
⟨127,1133070670,1133071552⟩,
⟨128,1142416319,1142417208⟩]
theorem checked11688 : checkPrefixCuts (2^48) 1535901697 9 Manual.Count131072.C011688.packed 128 cuts11688 = true := by
 decide +kernel
def pointBounds11688 : List (Nat × Nat × Nat) := [(1535935488,92976194972677,92976570638986),(1535983616,92976611698374,92976987365006),(1536031744,92977035374604,92977411041567)]
theorem point_links_checked11688 : (cuts11688.take 3).map (fun c => (1535901697-1+2*2^9*c.k,92975902303934+c.lower,92976277970015+c.upper)) = pointBounds11688 := by
 decide +kernel
def cuts11689 : List PrefixCut := [⟨46,396725669,396725976⟩,
⟨93,811946337,811946969⟩,
⟨128,1123261722,1123262598⟩]
theorem checked11689 : checkPrefixCuts (2^48) 1536032769 9 Manual.Count131072.C011689.packed 128 cuts11689 = true := by
 decide +kernel
def pointBounds11689 : List (Nat × Nat × Nat) := [(1536079872,92977441445922,92977817113199),(1536128000,92977856666590,92978232334192)]
theorem point_links_checked11689 : (cuts11689.take 2).map (fun c => (1536032769-1+2*2^9*c.k,92977044720253+c.lower,92977420387223+c.upper)) = pointBounds11689 := by
 decide +kernel
def cuts11690 : List PrefixCut := [⟨12,107740182,107740266⟩,
⟨59,518170910,518171313⟩,
⟨106,924008131,924008853⟩,
⟨128,1114005228,1114006099⟩]
theorem checked11690 : checkPrefixCuts (2^48) 1536163841 9 Manual.Count131072.C011690.packed 128 cuts11690 = true := by
 decide +kernel
def pointBounds11690 : List (Nat × Nat × Nat) := [(1536176128,92978275722157,92978651390087),(1536224256,92978686152885,92979061821134),(1536272384,92979091990106,92979467658674)]
theorem point_links_checked11690 : (cuts11690.take 3).map (fun c => (1536163841-1+2*2^9*c.k,92978167981975+c.lower,92978543649821+c.upper)) = pointBounds11690 := by
 decide +kernel
def cuts11691 : List PrefixCut := [⟨25,218575697,218575869⟩,
⟨72,628234992,628235485⟩,
⟨119,1051072053,1051072870⟩,
⟨128,1127833530,1127834406⟩]
theorem checked11691 : checkPrefixCuts (2^48) 1536294913 9 Manual.Count131072.C011691.packed 128 cuts11691 = true := by
 decide +kernel
def pointBounds11691 : List (Nat × Nat × Nat) := [(1536320512,92979500562900,92979876231789),(1536368640,92979910222195,92980285891405),(1536416768,92980333059256,92980708728790)]
theorem point_links_checked11691 : (cuts11691.take 3).map (fun c => (1536294913-1+2*2^9*c.k,92979281987203+c.lower,92979657655920+c.upper)) = pointBounds11691 := by
 decide +kernel
def cuts11692 : List PrefixCut := [⟨38,347528006,347528276⟩,
⟨85,769239564,769240164⟩,
⟨128,1148255589,1148256486⟩]
theorem checked11692 : checkPrefixCuts (2^48) 1536425985 9 Manual.Count131072.C011692.packed 128 cuts11692 = true := by
 decide +kernel
def pointBounds11692 : List (Nat × Nat × Nat) := [(1536464896,92980757348739,92981133018602),(1536513024,92981179060297,92981554730490)]
theorem point_links_checked11692 : (cuts11692.take 2).map (fun c => (1536425985-1+2*2^9*c.k,92980409820733+c.lower,92980785490326+c.upper)) = pointBounds11692 := by
 decide +kernel
def cuts11693 : List PrefixCut := [⟨4,37736148,37736177⟩,
⟨51,457772540,457772893⟩,
⟨98,876330483,876331159⟩,
⟨128,1150355270,1150356156⟩]
theorem checked11693 : checkPrefixCuts (2^48) 1536557057 9 Manual.Count131072.C011693.packed 128 cuts11693 = true := by
 decide +kernel
def pointBounds11693 : List (Nat × Nat × Nat) := [(1536561152,92981595812470,92981971482989),(1536609280,92982015848862,92982391519705),(1536657408,92982434406805,92982810077971)]
theorem point_links_checked11693 : (cuts11693.take 3).map (fun c => (1536557057-1+2*2^9*c.k,92981558076322+c.lower,92981933746812+c.upper)) = pointBounds11693 := by
 decide +kernel
def cuts11694 : List PrefixCut := [⟨17,144520176,144520291⟩,
⟨64,567447862,567448306⟩,
⟨111,978823279,978824040⟩,
⟨128,1129010567,1129011442⟩]
theorem checked11694 : checkPrefixCuts (2^48) 1536688129 9 Manual.Count131072.C011694.packed 128 cuts11694 = true := by
 decide +kernel
def pointBounds11694 : List (Nat × Nat × Nat) := [(1536705536,92982852951768,92983228623259),(1536753664,92983275879454,92983651551274),(1536801792,92983687254871,92984062927008)]
theorem point_links_checked11694 : (cuts11694.take 3).map (fun c => (1536688129-1+2*2^9*c.k,92982708431592+c.lower,92983084102968+c.upper)) = pointBounds11694 := by
 decide +kernel
def cuts11695 : List PrefixCut := [⟨30,274362225,274362441⟩,
⟨77,686627607,686628148⟩,
⟨124,1106388904,1106389768⟩,
⟨128,1143016669,1143017560⟩]
theorem checked11695 : checkPrefixCuts (2^48) 1536819201 9 Manual.Count131072.C011695.packed 128 cuts11695 = true := by
 decide +kernel
def pointBounds11695 : List (Nat × Nat × Nat) := [(1536849920,92984111804384,92984487476851),(1536898048,92984524069766,92984899742558),(1536946176,92984943831063,92985319504178)]
theorem point_links_checked11695 : (cuts11695.take 3).map (fun c => (1536819201-1+2*2^9*c.k,92983837442159+c.lower,92984213114410+c.upper)) = pointBounds11695 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000052
