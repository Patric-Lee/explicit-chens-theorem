import PlattAssemblyKernel
import PlattCertificates.Count131072.C018256
import PlattCertificates.Count131072.C018257
import PlattCertificates.Count131072.C018258
import PlattCertificates.Count131072.C018259
import PlattCertificates.Count131072.C018260
import PlattCertificates.Count131072.C018261
import PlattCertificates.Count131072.C018262
import PlattCertificates.Count131072.C018263
import PlattCertificates.Count131072.C018264
import PlattCertificates.Count131072.C018265
import PlattCertificates.Count131072.C018266
import PlattCertificates.Count131072.C018267
import PlattCertificates.Count131072.C018268
import PlattCertificates.Count131072.C018269
import PlattCertificates.Count131072.C018270
import PlattCertificates.Count131072.C018271
import PlattCertificates.Count131072.C018272
import PlattCertificates.Count131072.C018273
import PlattCertificates.Count131072.C018274
import PlattCertificates.Count131072.C018275
import PlattCertificates.Count131072.C018276
import PlattCertificates.Count131072.C018277
import PlattCertificates.Count131072.C018278
import PlattCertificates.Count131072.C018279
import PlattCertificates.Count131072.C018280
import PlattCertificates.Count131072.C018281
import PlattCertificates.Count131072.C018282
import PlattCertificates.Count131072.C018283
import PlattCertificates.Count131072.C018284
import PlattCertificates.Count131072.C018285
import PlattCertificates.Count131072.C018286
import PlattCertificates.Count131072.C018287
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000258
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts18256 : List PrefixCut := [⟨30,168758252,168758350⟩,
⟨104,573557638,573557983⟩,
⟨128,705434696,705435124⟩]
theorem checked18256 : checkPrefixCuts (2^48) 2396782593 9 Manual.Count131072.C018256.packed 128 cuts18256 = true := by
 decide +kernel
def pointBounds18256 : List (Nat × Nat × Nat) := [(2396813312,98836209067936,98836588730475),(2396889088,98836613867322,98836993530108)]
theorem point_links_checked18256 : (cuts18256.take 2).map (fun c => (2396782593-1+2*2^9*c.k,98836040309684+c.lower,98836419972125+c.upper)) = pointBounds18256 := by
 decide +kernel
def cuts18257 : List PrefixCut := [⟨50,275140804,275140968⟩,
⟨124,686725435,686725851⟩,
⟨128,708331800,708332229⟩]
theorem checked18257 : checkPrefixCuts (2^48) 2396913665 9 Manual.Count131072.C018257.packed 128 cuts18257 = true := by
 decide +kernel
def pointBounds18257 : List (Nat × Nat × Nat) := [(2396964864,98837020885184,98837400548217),(2397040640,98837432469815,98837812133100)]
theorem point_links_checked18257 : (cuts18257.take 2).map (fun c => (2396913665-1+2*2^9*c.k,98836745744380+c.lower,98837125407249+c.upper)) = pointBounds18257 := by
 decide +kernel
def cuts18258 : List PrefixCut := [⟨70,390317516,390317753⟩,
⟨128,720387463,720387896⟩]
theorem checked18258 : checkPrefixCuts (2^48) 2397044737 9 Manual.Count131072.C018258.packed 128 cuts18258 = true := by
 decide +kernel
def pointBounds18258 : List (Nat × Nat × Nat) := [(2397116416,98837844393696,98838224057231)]
theorem point_links_checked18258 : (cuts18258.take 1).map (fun c => (2397044737-1+2*2^9*c.k,98837454076180+c.lower,98837833739478+c.upper)) = pointBounds18258 := by
 decide +kernel
def cuts18259 : List PrefixCut := [⟨16,90647444,90647501⟩,
⟨90,500784074,500784381⟩,
⟨128,713890333,713890768⟩]
theorem checked18259 : checkPrefixCuts (2^48) 2397175809 9 Manual.Count131072.C018259.packed 128 cuts18259 = true := by
 decide +kernel
def pointBounds18259 : List (Nat × Nat × Nat) := [(2397192192,98838265111087,98838644774875),(2397267968,98838675247717,98839054911755)]
theorem point_links_checked18259 : (cuts18259.take 2).map (fun c => (2397175809-1+2*2^9*c.k,98838174463643+c.lower,98838554127374+c.upper)) = pointBounds18259 := by
 decide +kernel
def cuts18260 : List PrefixCut := [⟨36,198308931,198309050⟩,
⟨110,606775878,606776246⟩,
⟨128,707863287,707863718⟩]
theorem checked18260 : checkPrefixCuts (2^48) 2397306881 9 Manual.Count131072.C018260.packed 128 cuts18260 = true := by
 decide +kernel
def pointBounds18260 : List (Nat × Nat × Nat) := [(2397343744,98839086662907,98839466327192),(2397419520,98839495129854,98839874794388)]
theorem point_links_checked18260 : (cuts18260.take 2).map (fun c => (2397306881-1+2*2^9*c.k,98838888353976+c.lower,98839268018142+c.upper)) = pointBounds18260 := by
 decide +kernel
def cuts18261 : List PrefixCut := [⟨56,310419217,310419407⟩,
⟨128,715221072,715221513⟩]
theorem checked18261 : checkPrefixCuts (2^48) 2397437953 9 Manual.Count131072.C018261.packed 128 cuts18261 = true := by
 decide +kernel
def pointBounds18261 : List (Nat × Nat × Nat) := [(2397495296,98839906636480,98840286301267)]
theorem point_links_checked18261 : (cuts18261.take 1).map (fun c => (2397437953-1+2*2^9*c.k,98839596217263+c.lower,98839975881860+c.upper)) = pointBounds18261 := by
 decide +kernel
def cuts18262 : List PrefixCut := [⟨2,10683406,10683413⟩,
⟨76,408780568,408780822⟩,
⟨128,702855074,702855509⟩]
theorem checked18262 : checkPrefixCuts (2^48) 2397569025 9 Manual.Count131072.C018262.packed 128 cuts18262 = true := by
 decide +kernel
def pointBounds18262 : List (Nat × Nat × Nat) := [(2397571072,98840322121741,98840701786786),(2397646848,98840720218903,98841099884195)]
theorem point_links_checked18262 : (cuts18262.take 2).map (fun c => (2397569025-1+2*2^9*c.k,98840311438335+c.lower,98840691103373+c.upper)) = pointBounds18262 := by
 decide +kernel
def cuts18263 : List PrefixCut := [⟨22,124906310,124906386⟩,
⟨96,534599996,534600326⟩,
⟨128,716551529,716551971⟩]
theorem checked18263 : checkPrefixCuts (2^48) 2397700097 9 Manual.Count131072.C018263.packed 128 cuts18263 = true := by
 decide +kernel
def pointBounds18263 : List (Nat × Nat × Nat) := [(2397722624,98841139199719,98841518865268),(2397798400,98841548893405,98841928559208)]
theorem point_links_checked18263 : (cuts18263.take 2).map (fun c => (2397700097-1+2*2^9*c.k,98841014293409+c.lower,98841393958882+c.upper)) = pointBounds18263 := by
 decide +kernel
def cuts18264 : List PrefixCut := [⟨42,235946350,235946488⟩,
⟨116,647257487,647257868⟩,
⟨128,712169269,712169690⟩]
theorem checked18264 : checkPrefixCuts (2^48) 2397831169 9 Manual.Count131072.C018264.packed 128 cuts18264 = true := by
 decide +kernel
def pointBounds18264 : List (Nat × Nat × Nat) := [(2397874176,98841966791288,98842346457341),(2397949952,98842378102425,98842757768721)]
theorem point_links_checked18264 : (cuts18264.take 2).map (fun c => (2397831169-1+2*2^9*c.k,98841730844938+c.lower,98842110510853+c.upper)) = pointBounds18264 := by
 decide +kernel
def cuts18265 : List PrefixCut := [⟨62,345916802,345917011⟩,
⟨128,712717114,712717552⟩]
theorem checked18265 : checkPrefixCuts (2^48) 2397962241 9 Manual.Count131072.C018265.packed 128 cuts18265 = true := by
 decide +kernel
def pointBounds18265 : List (Nat × Nat × Nat) := [(2398025728,98842788931009,98843168597554)]
theorem point_links_checked18265 : (cuts18265.take 1).map (fun c => (2397962241-1+2*2^9*c.k,98842443014207+c.lower,98842822680543+c.upper)) = pointBounds18265 := by
 decide +kernel
def cuts18266 : List PrefixCut := [⟨8,44250091,44250116⟩,
⟨82,458691287,458691569⟩,
⟨128,714673505,714673942⟩]
theorem checked18266 : checkPrefixCuts (2^48) 2398093313 9 Manual.Count131072.C018266.packed 128 cuts18266 = true := by
 decide +kernel
def pointBounds18266 : List (Nat × Nat × Nat) := [(2398101504,98843199981412,98843579648211),(2398177280,98843614422608,98843994089664)]
theorem point_links_checked18266 : (cuts18266.take 2).map (fun c => (2398093313-1+2*2^9*c.k,98843155731321+c.lower,98843535398095+c.upper)) = pointBounds18266 := by
 decide +kernel
def cuts18267 : List PrefixCut := [⟨28,159032745,159032841⟩,
⟨102,573330456,573330798⟩,
⟨128,718859684,718860116⟩]
theorem checked18267 : checkPrefixCuts (2^48) 2398224385 9 Manual.Count131072.C018267.packed 128 cuts18267 = true := by
 decide +kernel
def pointBounds18267 : List (Nat × Nat × Nat) := [(2398253056,98844029437571,98844409104878),(2398328832,98844443735282,98844823402835)]
theorem point_links_checked18267 : (cuts18267.take 2).map (fun c => (2398224385-1+2*2^9*c.k,98843870404826+c.lower,98844250072037+c.upper)) = pointBounds18267 := by
 decide +kernel
def cuts18268 : List PrefixCut := [⟨48,265351890,265352054⟩,
⟨122,673051360,673051769⟩,
⟨128,706614994,706615423⟩]
theorem checked18268 : checkPrefixCuts (2^48) 2398355457 9 Manual.Count131072.C018268.packed 128 cuts18268 = true := by
 decide +kernel
def pointBounds18268 : List (Nat × Nat × Nat) := [(2398404608,98844854616400,98845234284207),(2398480384,98845262315870,98845641983922)]
theorem point_links_checked18268 : (cuts18268.take 2).map (fun c => (2398355457-1+2*2^9*c.k,98844589264510+c.lower,98844968932153+c.upper)) = pointBounds18268 := by
 decide +kernel
def cuts18269 : List PrefixCut := [⟨68,370250328,370250554⟩,
⟨128,707984458,707984889⟩]
theorem checked18269 : checkPrefixCuts (2^48) 2398486529 9 Manual.Count131072.C018269.packed 128 cuts18269 = true := by
 decide +kernel
def pointBounds18269 : List (Nat × Nat × Nat) := [(2398556160,98845666129832,98846045798130)]
theorem point_links_checked18269 : (cuts18269.take 1).map (fun c => (2398486529-1+2*2^9*c.k,98845295879504+c.lower,98845675547576+c.upper)) = pointBounds18269 := by
 decide +kernel
def cuts18270 : List PrefixCut := [⟨14,76745886,76745932⟩,
⟨88,492503623,492503927⟩,
⟨128,712522469,712522912⟩]
theorem checked18270 : checkPrefixCuts (2^48) 2398617601 9 Manual.Count131072.C018270.packed 128 cuts18270 = true := by
 decide +kernel
def pointBounds18270 : List (Nat × Nat × Nat) := [(2398631936,98846080609848,98846460278397),(2398707712,98846496367585,98846876036392)]
theorem point_links_checked18270 : (cuts18270.take 2).map (fun c => (2398617601-1+2*2^9*c.k,98846003863962+c.lower,98846383532465+c.upper)) = pointBounds18270 := by
 decide +kernel
def cuts18271 : List PrefixCut := [⟨34,185164953,185165067⟩,
⟨108,595968203,595968565⟩,
⟨128,702509737,702510164⟩]
theorem checked18271 : checkPrefixCuts (2^48) 2398748673 9 Manual.Count131072.C018271.packed 128 cuts18271 = true := by
 decide +kernel
def pointBounds18271 : List (Nat × Nat × Nat) := [(2398783488,98846901551384,98847281220444),(2398859264,98847312354634,98847692023942)]
theorem point_links_checked18271 : (cuts18271.take 2).map (fun c => (2398748673-1+2*2^9*c.k,98846716386431+c.lower,98847096055377+c.upper)) = pointBounds18271 := by
 decide +kernel
def cuts18272 : List PrefixCut := [⟨54,299907340,299907520⟩,
⟨128,715729913,715730347⟩]
theorem checked18272 : checkPrefixCuts (2^48) 2398879745 9 Manual.Count131072.C018272.packed 128 cuts18272 = true := by
 decide +kernel
def pointBounds18272 : List (Nat × Nat × Nat) := [(2398935040,98847718803508,98848098473061),(2399010816,98848134626081,98848514295888)]
theorem point_links_checked18272 : (cuts18272.take 2).map (fun c => (2398879745-1+2*2^9*c.k,98847418896168+c.lower,98847798565541+c.upper)) = pointBounds18272 := by
 decide +kernel
def cuts18273 : List PrefixCut := [⟨74,414988172,414988426⟩,
⟨128,713696322,713696760⟩]
theorem checked18273 : checkPrefixCuts (2^48) 2399010817 9 Manual.Count131072.C018273.packed 128 cuts18273 = true := by
 decide +kernel
def pointBounds18273 : List (Nat × Nat × Nat) := [(2399086592,98848549614253,98848929284314)]
theorem point_links_checked18273 : (cuts18273.take 1).map (fun c => (2399010817-1+2*2^9*c.k,98848134626081+c.lower,98848514295888+c.upper)) = pointBounds18273 := by
 decide +kernel
def cuts18274 : List PrefixCut := [⟨20,109579360,109579427⟩,
⟨94,520786993,520787309⟩,
⟨128,711545394,711545821⟩]
theorem checked18274 : checkPrefixCuts (2^48) 2399141889 9 Manual.Count131072.C018274.packed 128 cuts18274 = true := by
 decide +kernel
def pointBounds18274 : List (Nat × Nat × Nat) := [(2399162368,98848957901763,98849337572075),(2399238144,98849369109396,98849748779957)]
theorem point_links_checked18274 : (cuts18274.take 2).map (fun c => (2399141889-1+2*2^9*c.k,98848848322403+c.lower,98849227992648+c.upper)) = pointBounds18274 := by
 decide +kernel
def cuts18275 : List PrefixCut := [⟨40,219849710,219849847⟩,
⟨114,632321822,632322211⟩,
⟨128,711858463,711858898⟩]
theorem checked18275 : checkPrefixCuts (2^48) 2399272961 9 Manual.Count131072.C018275.packed 128 cuts18275 = true := by
 decide +kernel
def pointBounds18275 : List (Nat × Nat × Nat) := [(2399313920,98849779717507,98850159388316),(2399389696,98850192189619,98850571860680)]
theorem point_links_checked18275 : (cuts18275.take 2).map (fun c => (2399272961-1+2*2^9*c.k,98849559867797+c.lower,98849939538469+c.upper)) = pointBounds18275 := by
 decide +kernel
def cuts18276 : List PrefixCut := [⟨60,339843735,339843939⟩,
⟨128,720969688,720970125⟩]
theorem checked18276 : checkPrefixCuts (2^48) 2399404033 9 Manual.Count131072.C018276.packed 128 cuts18276 = true := by
 decide +kernel
def pointBounds18276 : List (Nat × Nat × Nat) := [(2399465472,98850611569995,98850991241306)]
theorem point_links_checked18276 : (cuts18276.take 1).map (fun c => (2399404033-1+2*2^9*c.k,98850271726260+c.lower,98850651397367+c.upper)) = pointBounds18276 := by
 decide +kernel
def cuts18277 : List PrefixCut := [⟨6,34018095,34018115⟩,
⟨80,442932124,442932395⟩,
⟨128,714244111,714244541⟩]
theorem checked18277 : checkPrefixCuts (2^48) 2399535105 9 Manual.Count131072.C018277.packed 128 cuts18277 = true := by
 decide +kernel
def pointBounds18277 : List (Nat × Nat × Nat) := [(2399541248,98851026714043,98851406385607),(2399617024,98851435628072,98851815299887)]
theorem point_links_checked18277 : (cuts18277.take 2).map (fun c => (2399535105-1+2*2^9*c.k,98850992695948+c.lower,98851372367492+c.upper)) = pointBounds18277 := by
 decide +kernel
def cuts18278 : List PrefixCut := [⟨26,146386497,146386587⟩,
⟨100,559966433,559966772⟩,
⟨128,718075799,718076234⟩]
theorem checked18278 : checkPrefixCuts (2^48) 2399666177 9 Manual.Count131072.C018278.packed 128 cuts18278 = true := by
 decide +kernel
def pointBounds18278 : List (Nat × Nat × Nat) := [(2399692800,98851853326556,98852232998620),(2399768576,98852266906492,98852646578805)]
theorem point_links_checked18278 : (cuts18278.take 2).map (fun c => (2399666177-1+2*2^9*c.k,98851706940059+c.lower,98852086612033+c.upper)) = pointBounds18278 := by
 decide +kernel
def cuts18279 : List PrefixCut := [⟨46,256982292,256982451⟩,
⟨120,676165909,676166320⟩,
⟨128,718740329,718740766⟩]
theorem checked18279 : checkPrefixCuts (2^48) 2399797249 9 Manual.Count131072.C018279.packed 128 cuts18279 = true := by
 decide +kernel
def pointBounds18279 : List (Nat × Nat × Nat) := [(2399844352,98852681998150,98853061670718),(2399920128,98853101181767,98853480854587)]
theorem point_links_checked18279 : (cuts18279.take 2).map (fun c => (2399797249-1+2*2^9*c.k,98852425015858+c.lower,98852804688267+c.upper)) = pointBounds18279 := by
 decide +kernel
def cuts18280 : List PrefixCut := [⟨66,366509527,366509744⟩,
⟨128,709553106,709553535⟩]
theorem checked18280 : checkPrefixCuts (2^48) 2399928321 9 Manual.Count131072.C018280.packed 128 cuts18280 = true := by
 decide +kernel
def pointBounds18280 : List (Nat × Nat × Nat) := [(2399995904,98853510265714,98853889938777)]
theorem point_links_checked18280 : (cuts18280.take 1).map (fun c => (2399928321-1+2*2^9*c.k,98853143756187+c.lower,98853523429033+c.upper)) = pointBounds18280 := by
 decide +kernel
def cuts18281 : List PrefixCut := [⟨12,64385625,64385662⟩,
⟨86,473326534,473326816⟩,
⟨128,710100613,710101032⟩]
theorem checked18281 : checkPrefixCuts (2^48) 2400059393 9 Manual.Count131072.C018281.packed 128 cuts18281 = true := by
 decide +kernel
def pointBounds18281 : List (Nat × Nat × Nat) := [(2400071680,98853917694918,98854297368230),(2400147456,98854326635827,98854706309384)]
theorem point_links_checked18281 : (cuts18281.take 2).map (fun c => (2400059393-1+2*2^9*c.k,98853853309293+c.lower,98854232982568+c.upper)) = pointBounds18281 := by
 decide +kernel
def cuts18282 : List PrefixCut := [⟨32,179776585,179776693⟩,
⟨106,578606538,578606891⟩,
⟨128,702791265,702791692⟩]
theorem checked18282 : checkPrefixCuts (2^48) 2400190465 9 Manual.Count131072.C018282.packed 128 cuts18282 = true := by
 decide +kernel
def pointBounds18282 : List (Nat × Nat × Nat) := [(2400223232,98854743186491,98855122860293),(2400299008,98855142016444,98855521690491)]
theorem point_links_checked18282 : (cuts18282.take 2).map (fun c => (2400190465-1+2*2^9*c.k,98854563409906+c.lower,98854943083600+c.upper)) = pointBounds18282 := by
 decide +kernel
def cuts18283 : List PrefixCut := [⟨52,289877101,289877273⟩,
⟨126,694193163,694193586⟩,
⟨128,704863745,704864174⟩]
theorem checked18283 : checkPrefixCuts (2^48) 2400321537 9 Manual.Count131072.C018283.packed 128 cuts18283 = true := by
 decide +kernel
def pointBounds18283 : List (Nat × Nat × Nat) := [(2400374784,98855556078272,98855935752565),(2400450560,98855960394334,98856340068878)]
theorem point_links_checked18283 : (cuts18283.take 2).map (fun c => (2400321537-1+2*2^9*c.k,98855266201171+c.lower,98855645875292+c.upper)) = pointBounds18283 := by
 decide +kernel
def cuts18284 : List PrefixCut := [⟨72,405358523,405358771⟩,
⟨128,710805430,710805863⟩]
theorem checked18284 : checkPrefixCuts (2^48) 2400452609 9 Manual.Count131072.C018284.packed 128 cuts18284 = true := by
 decide +kernel
def pointBounds18284 : List (Nat × Nat × Nat) := [(2400526336,98856376423439,98856756098237)]
theorem point_links_checked18284 : (cuts18284.take 1).map (fun c => (2400452609-1+2*2^9*c.k,98855971064916+c.lower,98856350739466+c.upper)) = pointBounds18284 := by
 decide +kernel
def cuts18285 : List PrefixCut := [⟨18,102478463,102478523⟩,
⟨92,511446239,511446543⟩,
⟨128,711469946,711470372⟩]
theorem checked18285 : checkPrefixCuts (2^48) 2400583681 9 Manual.Count131072.C018285.packed 128 cuts18285 = true := by
 decide +kernel
def pointBounds18285 : List (Nat × Nat × Nat) := [(2400602112,98856784348809,98857164023852),(2400677888,98857193316585,98857572991872)]
theorem point_links_checked18285 : (cuts18285.take 2).map (fun c => (2400583681-1+2*2^9*c.k,98856681870346+c.lower,98857061545329+c.upper)) = pointBounds18285 := by
 decide +kernel
def cuts18286 : List PrefixCut := [⟨38,207758721,207758849⟩,
⟨112,624438713,624439095⟩,
⟨128,710844808,710845244⟩]
theorem checked18286 : checkPrefixCuts (2^48) 2400714753 9 Manual.Count131072.C018286.packed 128 cuts18286 = true := by
 decide +kernel
def pointBounds18286 : List (Nat × Nat × Nat) := [(2400753664,98857601099013,98857980774550),(2400829440,98858017779005,98858397454796)]
theorem point_links_checked18286 : (cuts18286.take 2).map (fun c => (2400714753-1+2*2^9*c.k,98857393340292+c.lower,98857773015701+c.upper)) = pointBounds18286 := by
 decide +kernel
def cuts18287 : List PrefixCut := [⟨58,324281533,324281728⟩,
⟨128,708813121,708813551⟩]
theorem checked18287 : checkPrefixCuts (2^48) 2400845825 9 Manual.Count131072.C018287.packed 128 cuts18287 = true := by
 decide +kernel
def pointBounds18287 : List (Nat × Nat × Nat) := [(2400905216,98858428466633,98858808142673)]
theorem point_links_checked18287 : (cuts18287.take 1).map (fun c => (2400845825-1+2*2^9*c.k,98858104185100+c.lower,98858483860945+c.upper)) = pointBounds18287 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000258
