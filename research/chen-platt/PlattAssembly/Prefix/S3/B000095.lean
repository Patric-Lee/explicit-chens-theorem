import PlattAssemblyKernel
import PlattCertificates.Count131072.C023040
import PlattCertificates.Count131072.C023041
import PlattCertificates.Count131072.C023042
import PlattCertificates.Count131072.C023043
import PlattCertificates.Count131072.C023044
import PlattCertificates.Count131072.C023045
import PlattCertificates.Count131072.C023046
import PlattCertificates.Count131072.C023047
import PlattCertificates.Count131072.C023048
import PlattCertificates.Count131072.C023049
import PlattCertificates.Count131072.C023050
import PlattCertificates.Count131072.C023051
import PlattCertificates.Count131072.C023052
import PlattCertificates.Count131072.C023053
import PlattCertificates.Count131072.C023054
import PlattCertificates.Count131072.C023055
import PlattCertificates.Count131072.C023056
import PlattCertificates.Count131072.C023057
import PlattCertificates.Count131072.C023058
import PlattCertificates.Count131072.C023059
import PlattCertificates.Count131072.C023060
import PlattCertificates.Count131072.C023061
import PlattCertificates.Count131072.C023062
import PlattCertificates.Count131072.C023063
import PlattCertificates.Count131072.C023064
import PlattCertificates.Count131072.C023065
import PlattCertificates.Count131072.C023066
import PlattCertificates.Count131072.C023067
import PlattCertificates.Count131072.C023068
import PlattCertificates.Count131072.C023069
import PlattCertificates.Count131072.C023070
import PlattCertificates.Count131072.C023071
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000095
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts23040 : List PrefixCut := [⟨64,284000843,284001009⟩,
⟨128,556174040,556174363⟩]
theorem checked23040 : checkPrefixCuts (2^48) 3023831041 9 Manual.Count131072.C023040.packed 128 cuts23040 = true := by
 decide +kernel
def pointBounds23040 : List (Nat × Nat × Nat) := [(3023896576,101848878993771,101849260417989)]
theorem point_links_checked23040 : (cuts23040.take 1).map (fun c => (3023831041-1+2*2^9*c.k,101848594992928+c.lower,101848976416980+c.upper)) = pointBounds23040 := by
 decide +kernel
def cuts23041 : List PrefixCut := [⟨29,128917224,128917297⟩,
⟨122,540140713,540141014⟩,
⟨128,568343210,568343527⟩]
theorem checked23041 : checkPrefixCuts (2^48) 3023962113 9 Manual.Count131072.C023041.packed 128 cuts23041 = true := by
 decide +kernel
def pointBounds23041 : List (Nat × Nat × Nat) := [(3023991808,101849280084192,101849661508640),(3024087040,101849691307681,101850072732357)]
theorem point_links_checked23041 : (cuts23041.take 2).map (fun c => (3023962113-1+2*2^9*c.k,101849151166968+c.lower,101849532591343+c.upper)) = pointBounds23041 := by
 decide +kernel
def cuts23042 : List PrefixCut := [⟨87,377330377,377330593⟩,
⟨128,553240351,553240666⟩]
theorem checked23042 : checkPrefixCuts (2^48) 3024093185 9 Manual.Count131072.C023042.packed 128 cuts23042 = true := by
 decide +kernel
def pointBounds23042 : List (Nat × Nat × Nat) := [(3024182272,101850096840555,101850478265463)]
theorem point_links_checked23042 : (cuts23042.take 1).map (fun c => (3024093185-1+2*2^9*c.k,101849719510178+c.lower,101850100934870+c.upper)) = pointBounds23042 := by
 decide +kernel
def cuts23043 : List PrefixCut := [⟨52,228214026,228214160⟩,
⟨128,562895854,562896183⟩]
theorem checked23043 : checkPrefixCuts (2^48) 3024224257 9 Manual.Count131072.C023043.packed 128 cuts23043 = true := by
 decide +kernel
def pointBounds23043 : List (Nat × Nat × Nat) := [(3024277504,101850500964555,101850882389696)]
theorem point_links_checked23043 : (cuts23043.take 1).map (fun c => (3024224257-1+2*2^9*c.k,101850272750529+c.lower,101850654175536+c.upper)) = pointBounds23043 := by
 decide +kernel
def cuts23044 : List PrefixCut := [⟨17,72593914,72593954⟩,
⟨110,472132267,472132533⟩,
⟨128,551610319,551610632⟩]
theorem checked23044 : checkPrefixCuts (2^48) 3024355329 9 Manual.Count131072.C023044.packed 128 cuts23044 = true := by
 decide +kernel
def pointBounds23044 : List (Nat × Nat × Nat) := [(3024372736,101850908240297,101851289665673),(3024467968,101851307778650,101851689204252)]
theorem point_links_checked23044 : (cuts23044.take 2).map (fun c => (3024355329-1+2*2^9*c.k,101850835646383+c.lower,101851217071719+c.upper)) = pointBounds23044 := by
 decide +kernel
def cuts23045 : List PrefixCut := [⟨75,322932713,322932894⟩,
⟨128,547770899,547771207⟩]
theorem checked23045 : checkPrefixCuts (2^48) 3024486401 9 Manual.Count131072.C023045.packed 128 cuts23045 = true := by
 decide +kernel
def pointBounds23045 : List (Nat × Nat × Nat) := [(3024563200,101851710189415,101852091615245)]
theorem point_links_checked23045 : (cuts23045.take 1).map (fun c => (3024486401-1+2*2^9*c.k,101851387256702+c.lower,101851768682351+c.upper)) = pointBounds23045 := by
 decide +kernel
def cuts23046 : List PrefixCut := [⟨40,176256959,176257059⟩,
⟨128,558914195,558914516⟩]
theorem checked23046 : checkPrefixCuts (2^48) 3024617473 9 Manual.Count131072.C023046.packed 128 cuts23046 = true := by
 decide +kernel
def pointBounds23046 : List (Nat × Nat × Nat) := [(3024658432,101852111284560,101852492710617)]
theorem point_links_checked23046 : (cuts23046.take 1).map (fun c => (3024617473-1+2*2^9*c.k,101851935027601+c.lower,101852316453558+c.upper)) = pointBounds23046 := by
 decide +kernel
def cuts23047 : List PrefixCut := [⟨5,23264302,23264316⟩,
⟨98,437268960,437269211⟩,
⟨128,570242730,570243060⟩]
theorem checked23047 : checkPrefixCuts (2^48) 3024748545 9 Manual.Count131072.C023047.packed 128 cuts23047 = true := by
 decide +kernel
def pointBounds23047 : List (Nat × Nat × Nat) := [(3024753664,101852517206098,101852898632390),(3024848896,101852931210756,101853312637285)]
theorem point_links_checked23047 : (cuts23047.take 2).map (fun c => (3024748545-1+2*2^9*c.k,101852493941796+c.lower,101852875368074+c.upper)) = pointBounds23047 := by
 decide +kernel
def cuts23048 : List PrefixCut := [⟨63,267990509,267990659⟩,
⟨128,550770199,550770510⟩]
theorem checked23048 : checkPrefixCuts (2^48) 3024879617 9 Manual.Count131072.C023048.packed 128 cuts23048 = true := by
 decide +kernel
def pointBounds23048 : List (Nat × Nat × Nat) := [(3024944128,101853332175035,101853713601793)]
theorem point_links_checked23048 : (cuts23048.take 1).map (fun c => (3024879617-1+2*2^9*c.k,101853064184526+c.lower,101853445611134+c.upper)) = pointBounds23048 := by
 decide +kernel
def cuts23049 : List PrefixCut := [⟨28,124220131,124220202⟩,
⟨121,526368731,526369028⟩,
⟨128,554933640,554933952⟩]
theorem checked23049 : checkPrefixCuts (2^48) 3025010689 9 Manual.Count131072.C023049.packed 128 cuts23049 = true := by
 decide +kernel
def pointBounds23049 : List (Nat × Nat × Nat) := [(3025039360,101853739174856,101854120601846),(3025134592,101854141323456,101854522750672)]
theorem point_links_checked23049 : (cuts23049.take 2).map (fun c => (3025010689-1+2*2^9*c.k,101853614954725+c.lower,101853996381644+c.upper)) = pointBounds23049 := by
 decide +kernel
def cuts23050 : List PrefixCut := [⟨86,373384918,373385122⟩,
⟨128,556026007,556026317⟩]
theorem checked23050 : checkPrefixCuts (2^48) 3025141761 9 Manual.Count131072.C023050.packed 128 cuts23050 = true := by
 decide +kernel
def pointBounds23050 : List (Nat × Nat × Nat) := [(3025229824,101854543273283,101854924700718)]
theorem point_links_checked23050 : (cuts23050.take 1).map (fun c => (3025141761-1+2*2^9*c.k,101854169888365+c.lower,101854551315596+c.upper)) = pointBounds23050 := by
 decide +kernel
def cuts23051 : List PrefixCut := [⟨51,221436064,221436184⟩,
⟨128,556560157,556560466⟩]
theorem checked23051 : checkPrefixCuts (2^48) 3025272833 9 Manual.Count131072.C023051.packed 128 cuts23051 = true := by
 decide +kernel
def pointBounds23051 : List (Nat × Nat × Nat) := [(3025325056,101854947350436,101855328778097)]
theorem point_links_checked23051 : (cuts23051.take 1).map (fun c => (3025272833-1+2*2^9*c.k,101854725914372+c.lower,101855107341913+c.upper)) = pointBounds23051 := by
 decide +kernel
def cuts23052 : List PrefixCut := [⟨16,67730849,67730890⟩,
⟨109,474108437,474108718⟩,
⟨128,555512663,555512991⟩]
theorem checked23052 : checkPrefixCuts (2^48) 3025403905 9 Manual.Count131072.C023052.packed 128 cuts23052 = true := by
 decide +kernel
def pointBounds23052 : List (Nat × Nat × Nat) := [(3025420288,101855350205378,101855731633269),(3025515520,101855756582966,101856138011097)]
theorem point_links_checked23052 : (cuts23052.take 2).map (fun c => (3025403905-1+2*2^9*c.k,101855282474529+c.lower,101855663902379+c.upper)) = pointBounds23052 := by
 decide +kernel
def cuts23053 : List PrefixCut := [⟨74,325518770,325518952⟩,
⟨128,561442666,561442979⟩]
theorem checked23053 : checkPrefixCuts (2^48) 3025534977 9 Manual.Count131072.C023053.packed 128 cuts23053 = true := by
 decide +kernel
def pointBounds23053 : List (Nat × Nat × Nat) := [(3025610752,101856163505962,101856544934322)]
theorem point_links_checked23053 : (cuts23053.take 1).map (fun c => (3025534977-1+2*2^9*c.k,101855837987192+c.lower,101856219415370+c.upper)) = pointBounds23053 := by
 decide +kernel
def cuts23054 : List PrefixCut := [⟨39,167916376,167916478⟩,
⟨128,555557531,555557858⟩]
theorem checked23054 : checkPrefixCuts (2^48) 3025666049 9 Manual.Count131072.C023054.packed 128 cuts23054 = true := by
 decide +kernel
def pointBounds23054 : List (Nat × Nat × Nat) := [(3025705984,101856567346234,101856948774827)]
theorem point_links_checked23054 : (cuts23054.take 1).map (fun c => (3025666049-1+2*2^9*c.k,101856399429858+c.lower,101856780858349+c.upper)) = pointBounds23054 := by
 decide +kernel
def cuts23055 : List PrefixCut := [⟨4,17302645,17302656⟩,
⟨97,416466265,416466508⟩,
⟨128,552928793,552929115⟩]
theorem checked23055 : checkPrefixCuts (2^48) 3025797121 9 Manual.Count131072.C023055.packed 128 cuts23055 = true := by
 decide +kernel
def pointBounds23055 : List (Nat × Nat × Nat) := [(3025801216,101856972290034,101857353718863),(3025896448,101857371453654,101857752882715)]
theorem point_links_checked23055 : (cuts23055.take 2).map (fun c => (3025797121-1+2*2^9*c.k,101856954987389+c.lower,101857336416207+c.upper)) = pointBounds23055 := by
 decide +kernel
def cuts23056 : List PrefixCut := [⟨62,274688170,274688321⟩,
⟨128,563137059,563137374⟩]
theorem checked23056 : checkPrefixCuts (2^48) 3025928193 9 Manual.Count131072.C023056.packed 128 cuts23056 = true := by
 decide +kernel
def pointBounds23056 : List (Nat × Nat × Nat) := [(3025991680,101857782604352,101858164033643)]
theorem point_links_checked23056 : (cuts23056.take 1).map (fun c => (3025928193-1+2*2^9*c.k,101857507916182+c.lower,101857889345322+c.upper)) = pointBounds23056 := by
 decide +kernel
def cuts23057 : List PrefixCut := [⟨27,122130735,122130806⟩,
⟨120,530372135,530372438⟩,
⟨128,566182172,566182494⟩]
theorem checked23057 : checkPrefixCuts (2^48) 3026059265 9 Manual.Count131072.C023057.packed 128 cuts23057 = true := by
 decide +kernel
def pointBounds23057 : List (Nat × Nat × Nat) := [(3026086912,101858193183976,101858574613502),(3026182144,101858601425376,101858982855134)]
theorem point_links_checked23057 : (cuts23057.take 2).map (fun c => (3026059265-1+2*2^9*c.k,101858071053241+c.lower,101858452482696+c.upper)) = pointBounds23057 := by
 decide +kernel
def cuts23058 : List PrefixCut := [⟨85,370000230,370000439⟩,
⟨128,557972630,557972950⟩]
theorem checked23058 : checkPrefixCuts (2^48) 3026190337 9 Manual.Count131072.C023058.packed 128 cuts23058 = true := by
 decide +kernel
def pointBounds23058 : List (Nat × Nat × Nat) := [(3026277376,101859007235643,101859388665629)]
theorem point_links_checked23058 : (cuts23058.take 1).map (fun c => (3026190337-1+2*2^9*c.k,101858637235413+c.lower,101859018665190+c.upper)) = pointBounds23058 := by
 decide +kernel
def cuts23059 : List PrefixCut := [⟨50,214197724,214197852⟩,
⟨128,548368713,548369036⟩]
theorem checked23059 : checkPrefixCuts (2^48) 3026321409 9 Manual.Count131072.C023059.packed 128 cuts23059 = true := by
 decide +kernel
def pointBounds23059 : List (Nat × Nat × Nat) := [(3026372608,101859409405767,101859790835992)]
theorem point_links_checked23059 : (cuts23059.take 1).map (fun c => (3026321409-1+2*2^9*c.k,101859195208043+c.lower,101859576638140+c.upper)) = pointBounds23059 := by
 decide +kernel
def cuts23060 : List PrefixCut := [⟨15,68079417,68079452⟩,
⟨108,474595324,474595592⟩,
⟨128,562481441,562481758⟩]
theorem checked23060 : checkPrefixCuts (2^48) 3026452481 9 Manual.Count131072.C023060.packed 128 cuts23060 = true := by
 decide +kernel
def pointBounds23060 : List (Nat × Nat × Nat) := [(3026467840,101859811656173,101860193086628),(3026563072,101860218172080,101860599602768)]
theorem point_links_checked23060 : (cuts23060.take 2).map (fun c => (3026452481-1+2*2^9*c.k,101859743576756+c.lower,101860125007176+c.upper)) = pointBounds23060 := by
 decide +kernel
def cuts23061 : List PrefixCut := [⟨73,320477007,320477194⟩,
⟨128,552506289,552506607⟩]
theorem checked23061 : checkPrefixCuts (2^48) 3026583553 9 Manual.Count131072.C023061.packed 128 cuts23061 = true := by
 decide +kernel
def pointBounds23061 : List (Nat × Nat × Nat) := [(3026658304,101860626535204,101861007966128)]
theorem point_links_checked23061 : (cuts23061.take 1).map (fun c => (3026583553-1+2*2^9*c.k,101860306058197+c.lower,101860687488934+c.upper)) = pointBounds23061 := by
 decide +kernel
def cuts23062 : List PrefixCut := [⟨38,166928256,166928350⟩,
⟨128,556946080,556946398⟩]
theorem checked23062 : checkPrefixCuts (2^48) 3026714625 9 Manual.Count131072.C023062.packed 128 cuts23062 = true := by
 decide +kernel
def pointBounds23062 : List (Nat × Nat × Nat) := [(3026753536,101861025492742,101861406923891)]
theorem point_links_checked23062 : (cuts23062.take 1).map (fun c => (3026714625-1+2*2^9*c.k,101860858564486+c.lower,101861239995541+c.upper)) = pointBounds23062 := by
 decide +kernel
def cuts23063 : List PrefixCut := [⟨3,12740009,12740016⟩,
⟨96,419948767,419949002⟩,
⟨128,557944875,557945184⟩]
theorem checked23063 : checkPrefixCuts (2^48) 3026845697 9 Manual.Count131072.C023063.packed 128 cuts23063 = true := by
 decide +kernel
def pointBounds23063 : List (Nat × Nat × Nat) := [(3026848768,101861428250575,101861809681955),(3026944000,101861835459333,101862216890941)]
theorem point_links_checked23063 : (cuts23063.take 2).map (fun c => (3026845697-1+2*2^9*c.k,101861415510566+c.lower,101861796941939+c.upper)) = pointBounds23063 := by
 decide +kernel
def cuts23064 : List PrefixCut := [⟨61,268269897,268270047⟩,
⟨128,556711919,556712233⟩]
theorem checked23064 : checkPrefixCuts (2^48) 3026976769 9 Manual.Count131072.C023064.packed 128 cuts23064 = true := by
 decide +kernel
def pointBounds23064 : List (Nat × Nat × Nat) := [(3027039232,101862241725338,101862623157170)]
theorem point_links_checked23064 : (cuts23064.take 1).map (fun c => (3026976769-1+2*2^9*c.k,101861973455441+c.lower,101862354887123+c.upper)) = pointBounds23064 := by
 decide +kernel
def cuts23065 : List PrefixCut := [⟨26,113347925,113347987⟩,
⟨119,522656812,522657104⟩,
⟨128,563475417,563475734⟩]
theorem checked23065 : checkPrefixCuts (2^48) 3027107841 9 Manual.Count131072.C023065.packed 128 cuts23065 = true := by
 decide +kernel
def pointBounds23065 : List (Nat × Nat × Nat) := [(3027134464,101862643515285,101863024947343),(3027229696,101863052824172,101863434256460)]
theorem point_links_checked23065 : (cuts23065.take 2).map (fun c => (3027107841-1+2*2^9*c.k,101862530167360+c.lower,101862911599356+c.upper)) = pointBounds23065 := by
 decide +kernel
def cuts23066 : List PrefixCut := [⟨84,364293311,364293522⟩,
⟨128,554339117,554339437⟩]
theorem checked23066 : checkPrefixCuts (2^48) 3027238913 9 Manual.Count131072.C023066.packed 128 cuts23066 = true := by
 decide +kernel
def pointBounds23066 : List (Nat × Nat × Nat) := [(3027324928,101863457936088,101863839368612)]
theorem point_links_checked23066 : (cuts23066.take 1).map (fun c => (3027238913-1+2*2^9*c.k,101863093642777+c.lower,101863475075090+c.upper)) = pointBounds23066 := by
 decide +kernel
def cuts23067 : List PrefixCut := [⟨49,211613224,211613346⟩,
⟨128,557662148,557662468⟩]
theorem checked23067 : checkPrefixCuts (2^48) 3027369985 9 Manual.Count131072.C023067.packed 128 cuts23067 = true := by
 decide +kernel
def pointBounds23067 : List (Nat × Nat × Nat) := [(3027420160,101863859595118,101864241027873)]
theorem point_links_checked23067 : (cuts23067.take 1).map (fun c => (3027369985-1+2*2^9*c.k,101863647981894+c.lower,101864029414527+c.upper)) = pointBounds23067 := by
 decide +kernel
def cuts23068 : List PrefixCut := [⟨14,59316433,59316465⟩,
⟨107,460671263,460671526⟩,
⟨128,548898835,548899148⟩]
theorem checked23068 : checkPrefixCuts (2^48) 3027501057 9 Manual.Count131072.C023068.packed 128 cuts23068 = true := by
 decide +kernel
def pointBounds23068 : List (Nat × Nat × Nat) := [(3027515392,101864264960475,101864646393460),(3027610624,101864666315305,101865047748521)]
theorem point_links_checked23068 : (cuts23068.take 2).map (fun c => (3027501057-1+2*2^9*c.k,101864205644042+c.lower,101864587076995+c.upper)) = pointBounds23068 := by
 decide +kernel
def cuts23069 : List PrefixCut := [⟨72,317112196,317112381⟩,
⟨128,562727095,562727414⟩]
theorem checked23069 : checkPrefixCuts (2^48) 3027632129 9 Manual.Count131072.C023069.packed 128 cuts23069 = true := by
 decide +kernel
def pointBounds23069 : List (Nat × Nat × Nat) := [(3027705856,101865071655073,101865453088524)]
theorem point_links_checked23069 : (cuts23069.take 1).map (fun c => (3027632129-1+2*2^9*c.k,101864754542877+c.lower,101865135976143+c.upper)) = pointBounds23069 := by
 decide +kernel
def cuts23070 : List PrefixCut := [⟨37,158038884,158038974⟩,
⟨128,558240446,558240761⟩]
theorem checked23070 : checkPrefixCuts (2^48) 3027763201 9 Manual.Count131072.C023070.packed 128 cuts23070 = true := by
 decide +kernel
def pointBounds23070 : List (Nat × Nat × Nat) := [(3027801088,101865475308856,101865856742531)]
theorem point_links_checked23070 : (cuts23070.take 1).map (fun c => (3027763201-1+2*2^9*c.k,101865317269972+c.lower,101865698703557+c.upper)) = pointBounds23070 := by
 decide +kernel
def cuts23071 : List PrefixCut := [⟨2,9946782,9946787⟩,
⟨95,410135631,410135860⟩,
⟨128,553661384,553661694⟩]
theorem checked23071 : checkPrefixCuts (2^48) 3027894273 9 Manual.Count131072.C023071.packed 128 cuts23071 = true := by
 decide +kernel
def pointBounds23071 : List (Nat × Nat × Nat) := [(3027896320,101865885457200,101866266891105),(3027991552,101866285646049,101866667080178)]
theorem point_links_checked23071 : (cuts23071.take 2).map (fun c => (3027894273-1+2*2^9*c.k,101865875510418+c.lower,101866256944318+c.upper)) = pointBounds23071 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000095
