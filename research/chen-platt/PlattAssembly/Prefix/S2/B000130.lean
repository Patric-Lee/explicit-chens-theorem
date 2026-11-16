import PlattAssemblyKernel
import PlattCertificates.Count131072.C014160
import PlattCertificates.Count131072.C014161
import PlattCertificates.Count131072.C014162
import PlattCertificates.Count131072.C014163
import PlattCertificates.Count131072.C014164
import PlattCertificates.Count131072.C014165
import PlattCertificates.Count131072.C014166
import PlattCertificates.Count131072.C014167
import PlattCertificates.Count131072.C014168
import PlattCertificates.Count131072.C014169
import PlattCertificates.Count131072.C014170
import PlattCertificates.Count131072.C014171
import PlattCertificates.Count131072.C014172
import PlattCertificates.Count131072.C014173
import PlattCertificates.Count131072.C014174
import PlattCertificates.Count131072.C014175
import PlattCertificates.Count131072.C014176
import PlattCertificates.Count131072.C014177
import PlattCertificates.Count131072.C014178
import PlattCertificates.Count131072.C014179
import PlattCertificates.Count131072.C014180
import PlattCertificates.Count131072.C014181
import PlattCertificates.Count131072.C014182
import PlattCertificates.Count131072.C014183
import PlattCertificates.Count131072.C014184
import PlattCertificates.Count131072.C014185
import PlattCertificates.Count131072.C014186
import PlattCertificates.Count131072.C014187
import PlattCertificates.Count131072.C014188
import PlattCertificates.Count131072.C014189
import PlattCertificates.Count131072.C014190
import PlattCertificates.Count131072.C014191
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000130
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts14160 : List PrefixCut := [⟨29,210963170,210963319⟩,
⟨86,629247549,629247982⟩,
⟨128,944011613,944012262⟩]
theorem checked14160 : checkPrefixCuts (2^48) 1859911681 9 Manual.Count131072.C014160.packed 128 cuts14160 = true := by
 decide +kernel
def pointBounds14160 : List (Nat × Nat × Nat) := [(1859941376,95511638006967,95512015528570),(1859999744,95512056291346,95512433813233)]
theorem point_links_checked14160 : (cuts14160.take 2).map (fun c => (1859911681-1+2*2^9*c.k,95511427043797+c.lower,95511804565251+c.upper)) = pointBounds14160 := by
 decide +kernel
def cuts14161 : List PrefixCut := [⟨15,104566603,104566676⟩,
⟨72,524791866,524792230⟩,
⟨128,916404889,916405529⟩]
theorem checked14161 : checkPrefixCuts (2^48) 1860042753 9 Manual.Count131072.C014161.packed 128 cuts14161 = true := by
 decide +kernel
def pointBounds14161 : List (Nat × Nat × Nat) := [(1860058112,95512475622013,95512853144189),(1860116480,95512895847276,95513273369743)]
theorem point_links_checked14161 : (cuts14161.take 2).map (fun c => (1860042753-1+2*2^9*c.k,95512371055410+c.lower,95512748577513+c.upper)) = pointBounds14161 := by
 decide +kernel
def cuts14162 : List PrefixCut := [⟨1,8019769,8019775⟩,
⟨58,424738440,424738729⟩,
⟨115,840990145,840990722⟩,
⟨128,931320018,931320658⟩]
theorem checked14162 : checkPrefixCuts (2^48) 1860173825 9 Manual.Count131072.C014162.packed 128 cuts14162 = true := by
 decide +kernel
def pointBounds14162 : List (Nat × Nat × Nat) := [(1860174848,95513295480068,95513673002817),(1860233216,95513712198739,95514089721771),(1860291584,95514128450444,95514505973764)]
theorem point_links_checked14162 : (cuts14162.take 3).map (fun c => (1860173825-1+2*2^9*c.k,95513287460299+c.lower,95513664983042+c.upper)) = pointBounds14162 := by
 decide +kernel
def cuts14163 : List PrefixCut := [⟨44,321672166,321672386⟩,
⟨101,729122404,729122903⟩,
⟨128,923538065,923538699⟩]
theorem checked14163 : checkPrefixCuts (2^48) 1860304897 9 Manual.Count131072.C014163.packed 128 cuts14163 = true := by
 decide +kernel
def pointBounds14163 : List (Nat × Nat × Nat) := [(1860349952,95514540452483,95514917976086),(1860408320,95514947902721,95515325426603)]
theorem point_links_checked14163 : (cuts14163.take 2).map (fun c => (1860304897-1+2*2^9*c.k,95514218780317+c.lower,95514596303700+c.upper)) = pointBounds14163 := by
 decide +kernel
def cuts14164 : List PrefixCut := [⟨30,214686022,214686170⟩,
⟨87,629070049,629070478⟩,
⟨128,931188520,931189152⟩]
theorem checked14164 : checkPrefixCuts (2^48) 1860435969 9 Manual.Count131072.C014164.packed 128 cuts14164 = true := by
 decide +kernel
def pointBounds14164 : List (Nat × Nat × Nat) := [(1860466688,95515357004404,95515734528569),(1860525056,95515771388431,95516148912877)]
theorem point_links_checked14164 : (cuts14164.take 2).map (fun c => (1860435969-1+2*2^9*c.k,95515142318382+c.lower,95515519842399+c.upper)) = pointBounds14164 := by
 decide +kernel
def cuts14165 : List PrefixCut := [⟨16,116488531,116488612⟩,
⟨73,536595205,536595576⟩,
⟨128,930971966,930972608⟩]
theorem checked14165 : checkPrefixCuts (2^48) 1860567041 9 Manual.Count131072.C014165.packed 128 cuts14165 = true := by
 decide +kernel
def pointBounds14165 : List (Nat × Nat × Nat) := [(1860583424,95516189995433,95516567520163),(1860641792,95516610102107,95516987627127)]
theorem point_links_checked14165 : (cuts14165.take 2).map (fun c => (1860567041-1+2*2^9*c.k,95516073506902+c.lower,95516451031551+c.upper)) = pointBounds14165 := by
 decide +kernel
def cuts14166 : List PrefixCut := [⟨2,13917182,13917192⟩,
⟨59,427644011,427644307⟩,
⟨116,846349788,846350372⟩,
⟨128,933931442,933932084⟩]
theorem checked14166 : checkPrefixCuts (2^48) 1860698113 9 Manual.Count131072.C014166.packed 128 cuts14166 = true := by
 decide +kernel
def pointBounds14166 : List (Nat × Nat × Nat) := [(1860700160,95517018396050,95517395921351),(1860758528,95517432122879,95517809648466),(1860816896,95517850828656,95518228354531)]
theorem point_links_checked14166 : (cuts14166.take 3).map (fun c => (1860698113-1+2*2^9*c.k,95517004478868+c.lower,95517382004159+c.upper)) = pointBounds14166 := by
 decide +kernel
def cuts14167 : List PrefixCut := [⟨45,324606652,324606874⟩,
⟨102,742529760,742530272⟩,
⟨128,925395341,925395978⟩]
theorem checked14167 : checkPrefixCuts (2^48) 1860829185 9 Manual.Count131072.C014167.packed 128 cuts14167 = true := by
 decide +kernel
def pointBounds14167 : List (Nat × Nat × Nat) := [(1860875264,95518263016962,95518640543117),(1860933632,95518680940070,95519058466515)]
theorem point_links_checked14167 : (cuts14167.take 2).map (fun c => (1860829185-1+2*2^9*c.k,95517938410310+c.lower,95518315936243+c.upper)) = pointBounds14167 := by
 decide +kernel
def cuts14168 : List PrefixCut := [⟨31,223398050,223398203⟩,
⟨88,641295083,641295519⟩,
⟨128,935312470,935313110⟩]
theorem checked14168 : checkPrefixCuts (2^48) 1860960257 9 Manual.Count131072.C014168.packed 128 cuts14168 = true := by
 decide +kernel
def pointBounds14168 : List (Nat × Nat × Nat) := [(1860992000,95519087203701,95519464730424),(1861050368,95519505100734,95519882627740)]
theorem point_links_checked14168 : (cuts14168.take 2).map (fun c => (1860960257-1+2*2^9*c.k,95518863805651+c.lower,95519241332221+c.upper)) = pointBounds14168 := by
 decide +kernel
def cuts14169 : List PrefixCut := [⟨17,115548226,115548310⟩,
⟨74,535687474,535687846⟩,
⟨128,921181537,921182174⟩]
theorem checked14169 : checkPrefixCuts (2^48) 1861091329 9 Manual.Count131072.C014169.packed 128 cuts14169 = true := by
 decide +kernel
def pointBounds14169 : List (Nat × Nat × Nat) := [(1861108736,95519914666347,95520292193641),(1861167104,95520334805595,95520712333177)]
theorem point_links_checked14169 : (cuts14169.take 2).map (fun c => (1861091329-1+2*2^9*c.k,95519799118121+c.lower,95520176645331+c.upper)) = pointBounds14169 := by
 decide +kernel
def cuts14170 : List PrefixCut := [⟨3,21626042,21626057⟩,
⟨60,444612344,444612650⟩,
⟨117,858663160,858663752⟩,
⟨128,937298079,937298726⟩]
theorem checked14170 : checkPrefixCuts (2^48) 1861222401 9 Manual.Count131072.C014170.packed 128 cuts14170 = true := by
 decide +kernel
def pointBounds14170 : List (Nat × Nat × Nat) := [(1861225472,95520741925700,95521119453562),(1861283840,95521164912002,95521542440155),(1861342208,95521578962818,95521956491257)]
theorem point_links_checked14170 : (cuts14170.take 3).map (fun c => (1861222401-1+2*2^9*c.k,95520720299658+c.lower,95521097827505+c.upper)) = pointBounds14170 := by
 decide +kernel
def cuts14171 : List PrefixCut := [⟨46,329202974,329203200⟩,
⟨103,750788501,750789014⟩,
⟨128,926344428,926345062⟩]
theorem checked14171 : checkPrefixCuts (2^48) 1861353473 9 Manual.Count131072.C014171.packed 128 cuts14171 = true := by
 decide +kernel
def pointBounds14171 : List (Nat × Nat × Nat) := [(1861400576,95521986800711,95522364329431),(1861458944,95522408386238,95522785915245)]
theorem point_links_checked14171 : (cuts14171.take 2).map (fun c => (1861353473-1+2*2^9*c.k,95521657597737+c.lower,95522035126231+c.upper)) = pointBounds14171 := by
 decide +kernel
def cuts14172 : List PrefixCut := [⟨32,231349127,231349291⟩,
⟨89,648372133,648372580⟩,
⟨128,935502558,935503201⟩]
theorem checked14172 : checkPrefixCuts (2^48) 1861484545 9 Manual.Count131072.C014172.packed 128 cuts14172 = true := by
 decide +kernel
def pointBounds14172 : List (Nat × Nat × Nat) := [(1861517312,95522815291292,95523192820584),(1861575680,95523232314298,95523609843873)]
theorem point_links_checked14172 : (cuts14172.take 2).map (fun c => (1861484545-1+2*2^9*c.k,95522583942165+c.lower,95522961471293+c.upper)) = pointBounds14172 := by
 decide +kernel
def cuts14173 : List PrefixCut := [⟨18,130333103,130333192⟩,
⟨75,541282221,541282594⟩,
⟨128,930900972,930901612⟩]
theorem checked14173 : checkPrefixCuts (2^48) 1861615617 9 Manual.Count131072.C014173.packed 128 cuts14173 = true := by
 decide +kernel
def pointBounds14173 : List (Nat × Nat × Nat) := [(1861634048,95523649777826,95524027307686),(1861692416,95524060726944,95524438257088)]
theorem point_links_checked14173 : (cuts14173.take 2).map (fun c => (1861615617-1+2*2^9*c.k,95523519444723+c.lower,95523896974494+c.upper)) = pointBounds14173 := by
 decide +kernel
def cuts14174 : List PrefixCut := [⟨4,26760353,26760371⟩,
⟨61,438590748,438591048⟩,
⟨118,843605047,843605620⟩,
⟨128,917380096,917380721⟩]
theorem checked14174 : checkPrefixCuts (2^48) 1861746689 9 Manual.Count131072.C014174.packed 128 cuts14174 = true := by
 decide +kernel
def pointBounds14174 : List (Nat × Nat × Nat) := [(1861750784,95524477106048,95524854636477),(1861809152,95524888936443,95525266467154),(1861867520,95525293950742,95525671481726)]
theorem point_links_checked14174 : (cuts14174.take 3).map (fun c => (1861746689-1+2*2^9*c.k,95524450345695+c.lower,95524827876106+c.upper)) = pointBounds14174 := by
 decide +kernel
def cuts14175 : List PrefixCut := [⟨47,340145986,340146215⟩,
⟨104,749367777,749368289⟩,
⟨128,920339136,920339766⟩]
theorem checked14175 : checkPrefixCuts (2^48) 1861877761 9 Manual.Count131072.C014175.packed 128 cuts14175 = true := by
 decide +kernel
def pointBounds14175 : List (Nat × Nat × Nat) := [(1861925888,95525707871777,95526085403042),(1861984256,95526117093568,95526494625116)]
theorem point_links_checked14175 : (cuts14175.take 2).map (fun c => (1861877761-1+2*2^9*c.k,95525367725791+c.lower,95525745256827+c.upper)) = pointBounds14175 := by
 decide +kernel
def cuts14176 : List PrefixCut := [⟨33,236725849,236726014⟩,
⟨90,646677739,646678183⟩,
⟨128,918762558,918763193⟩]
theorem checked14176 : checkPrefixCuts (2^48) 1862008833 9 Manual.Count131072.C014176.packed 128 cuts14176 = true := by
 decide +kernel
def pointBounds14176 : List (Nat × Nat × Nat) := [(1862042624,95526524790776,95526902322607),(1862100992,95526934742666,95527312274776)]
theorem point_links_checked14176 : (cuts14176.take 2).map (fun c => (1862008833-1+2*2^9*c.k,95526288064927+c.lower,95526665596593+c.upper)) = pointBounds14176 := by
 decide +kernel
def cuts14177 : List PrefixCut := [⟨19,139214584,139214679⟩,
⟨76,552617285,552617666⟩,
⟨128,926709034,926709674⟩]
theorem checked14177 : checkPrefixCuts (2^48) 1862139905 9 Manual.Count131072.C014177.packed 128 cuts14177 = true := by
 decide +kernel
def pointBounds14177 : List (Nat × Nat × Nat) := [(1862159360,95527346042069,95527723574465),(1862217728,95527759444770,95528136977452)]
theorem point_links_checked14177 : (cuts14177.take 2).map (fun c => (1862139905-1+2*2^9*c.k,95527206827485+c.lower,95527584359786+c.upper)) = pointBounds14177 := by
 decide +kernel
def cuts14178 : List PrefixCut := [⟨5,32647498,32647520⟩,
⟨62,453883774,453884086⟩,
⟨119,868910212,868910808⟩,
⟨128,936014497,936015139⟩]
theorem checked14178 : checkPrefixCuts (2^48) 1862270977 9 Manual.Count131072.C014178.packed 128 cuts14178 = true := by
 decide +kernel
def pointBounds14178 : List (Nat × Nat × Nat) := [(1862276096,95528166184017,95528543716980),(1862334464,95528587420293,95528964953546),(1862392832,95529002446731,95529379980268)]
theorem point_links_checked14178 : (cuts14178.take 3).map (fun c => (1862270977-1+2*2^9*c.k,95528133536519+c.lower,95528511069460+c.upper)) = pointBounds14178 := by
 decide +kernel
def cuts14179 : List PrefixCut := [⟨48,348513667,348513906⟩,
⟨105,764874183,764874708⟩,
⟨128,932170361,932170999⟩]
theorem checked14179 : checkPrefixCuts (2^48) 1862402049 9 Manual.Count131072.C014179.packed 128 cuts14179 = true := by
 decide +kernel
def pointBounds14179 : List (Nat × Nat × Nat) := [(1862451200,95529418064683,95529795598505),(1862509568,95529834425199,95530211959307)]
theorem point_links_checked14179 : (cuts14179.take 2).map (fun c => (1862402049-1+2*2^9*c.k,95529069551016+c.lower,95529447084599+c.upper)) = pointBounds14179 := by
 decide +kernel
def cuts14180 : List PrefixCut := [⟨34,242099621,242099789⟩,
⟨91,657527228,657527686⟩,
⟨128,924850838,924851473⟩]
theorem checked14180 : checkPrefixCuts (2^48) 1862533121 9 Manual.Count131072.C014180.packed 128 cuts14180 = true := by
 decide +kernel
def pointBounds14180 : List (Nat × Nat × Nat) := [(1862567936,95530243820998,95530621355387),(1862626304,95530659248605,95531036783284)]
theorem point_links_checked14180 : (cuts14180.take 2).map (fun c => (1862533121-1+2*2^9*c.k,95530001721377+c.lower,95530379255598+c.upper)) = pointBounds14180 := by
 decide +kernel
def cuts14181 : List PrefixCut := [⟨20,139779817,139779916⟩,
⟨77,552763717,552764098⟩,
⟨128,922368099,922368736⟩]
theorem checked14181 : checkPrefixCuts (2^48) 1862664193 9 Manual.Count131072.C014181.packed 128 cuts14181 = true := by
 decide +kernel
def pointBounds14181 : List (Nat × Nat × Nat) := [(1862684672,95531066352032,95531443886987),(1862743040,95531479335932,95531856871169)]
theorem point_links_checked14181 : (cuts14181.take 2).map (fun c => (1862664193-1+2*2^9*c.k,95530926572215+c.lower,95531304107071+c.upper)) = pointBounds14181 := by
 decide +kernel
def cuts14182 : List PrefixCut := [⟨6,44575456,44575488⟩,
⟨63,459497664,459497989⟩,
⟨120,873198196,873198807⟩,
⟨128,931066893,931067545⟩]
theorem checked14182 : checkPrefixCuts (2^48) 1862795265 9 Manual.Count131072.C014182.packed 128 cuts14182 = true := by
 decide +kernel
def pointBounds14182 : List (Nat × Nat × Nat) := [(1862801408,95531893515770,95532271051295),(1862859776,95532308437978,95532685973796),(1862918144,95532722138510,95533099674614)]
theorem point_links_checked14182 : (cuts14182.take 3).map (fun c => (1862795265-1+2*2^9*c.k,95531848940314+c.lower,95532226475807+c.upper)) = pointBounds14182 := by
 decide +kernel
def cuts14183 : List PrefixCut := [⟨49,360653827,360654073⟩,
⟨106,769191576,769192101⟩,
⟨128,932059211,932059849⟩]
theorem checked14183 : checkPrefixCuts (2^48) 1862926337 9 Manual.Count131072.C014183.packed 128 cuts14183 = true := by
 decide +kernel
def pointBounds14183 : List (Nat × Nat × Nat) := [(1862976512,95533140661034,95533518197425),(1863034880,95533549198783,95533926735453)]
theorem point_links_checked14183 : (cuts14183.take 2).map (fun c => (1862926337-1+2*2^9*c.k,95532780007207+c.lower,95533157543352+c.upper)) = pointBounds14183 := by
 decide +kernel
def cuts14184 : List PrefixCut := [⟨35,249887570,249887742⟩,
⟨92,669579364,669579824⟩,
⟨128,930482584,930483224⟩]
theorem checked14184 : checkPrefixCuts (2^48) 1863057409 9 Manual.Count131072.C014184.packed 128 cuts14184 = true := by
 decide +kernel
def pointBounds14184 : List (Nat × Nat × Nat) := [(1863093248,95533961953988,95534339490943),(1863151616,95534381645782,95534759183025)]
theorem point_links_checked14184 : (cuts14184.take 2).map (fun c => (1863057409-1+2*2^9*c.k,95533712066418+c.lower,95534089603201+c.upper)) = pointBounds14184 := by
 decide +kernel
def cuts14185 : List PrefixCut := [⟨21,154998581,154998688⟩,
⟨78,559557369,559557758⟩,
⟨128,923770439,923771078⟩]
theorem checked14185 : checkPrefixCuts (2^48) 1863188481 9 Manual.Count131072.C014185.packed 128 cuts14185 = true := by
 decide +kernel
def pointBounds14185 : List (Nat × Nat × Nat) := [(1863209984,95534797547583,95535175085113),(1863268352,95535202106371,95535579644183)]
theorem point_links_checked14185 : (cuts14185.take 2).map (fun c => (1863188481-1+2*2^9*c.k,95534642549002+c.lower,95535020086425+c.upper)) = pointBounds14185 := by
 decide +kernel
def cuts14186 : List PrefixCut := [⟨7,49245785,49245819⟩,
⟨64,475833655,475833973⟩,
⟨121,894704505,894705112⟩,
⟨128,943191764,943192405⟩]
theorem checked14186 : checkPrefixCuts (2^48) 1863319553 9 Manual.Count131072.C014186.packed 128 cuts14186 = true := by
 decide +kernel
def pointBounds14186 : List (Nat × Nat × Nat) := [(1863326720,95535615565226,95535993103322),(1863385088,95536042153096,95536419691476),(1863443456,95536461023946,95536838562615)]
theorem point_links_checked14186 : (cuts14186.take 3).map (fun c => (1863319553-1+2*2^9*c.k,95535566319441+c.lower,95535943857503+c.upper)) = pointBounds14186 := by
 decide +kernel
def cuts14187 : List PrefixCut := [⟨50,359041774,359042018⟩,
⟨107,770334144,770334672⟩,
⟨128,928020530,928021166⟩]
theorem checked14187 : checkPrefixCuts (2^48) 1863450625 9 Manual.Count131072.C014187.packed 128 cuts14187 = true := by
 decide +kernel
def pointBounds14187 : List (Nat × Nat × Nat) := [(1863501824,95536868552979,95537246091926),(1863560192,95537279845349,95537657384580)]
theorem point_links_checked14187 : (cuts14187.take 2).map (fun c => (1863450625-1+2*2^9*c.k,95536509511205+c.lower,95536887049908+c.upper)) = pointBounds14187 := by
 decide +kernel
def cuts14188 : List PrefixCut := [⟨36,260692012,260692192⟩,
⟨93,680567627,680568096⟩,
⟨128,934601013,934601652⟩]
theorem checked14188 : checkPrefixCuts (2^48) 1863581697 9 Manual.Count131072.C014188.packed 128 cuts14188 = true := by
 decide +kernel
def pointBounds14188 : List (Nat × Nat × Nat) := [(1863618560,95537698223747,95538075763266),(1863676928,95538118099362,95538495639170)]
theorem point_links_checked14188 : (cuts14188.take 2).map (fun c => (1863581697-1+2*2^9*c.k,95537437531735+c.lower,95537815071074+c.upper)) = pointBounds14188 := by
 decide +kernel
def cuts14189 : List PrefixCut := [⟨22,156163158,156163265⟩,
⟨79,572840945,572841336⟩,
⟨128,920943216,920943849⟩]
theorem checked14189 : checkPrefixCuts (2^48) 1863712769 9 Manual.Count131072.C014189.packed 128 cuts14189 = true := by
 decide +kernel
def pointBounds14189 : List (Nat × Nat × Nat) := [(1863735296,95538528295906,95538905835991),(1863793664,95538944973693,95539322514062)]
theorem point_links_checked14189 : (cuts14189.take 2).map (fun c => (1863712769-1+2*2^9*c.k,95538372132748+c.lower,95538749672726+c.upper)) = pointBounds14189 := by
 decide +kernel
def cuts14190 : List PrefixCut := [⟨8,54819593,54819631⟩,
⟨65,473434412,473434729⟩,
⟨122,889015969,889016570⟩,
⟨128,928429087,928429715⟩]
theorem checked14190 : checkPrefixCuts (2^48) 1863843841 9 Manual.Count131072.C014190.packed 128 cuts14190 = true := by
 decide +kernel
def pointBounds14190 : List (Nat × Nat × Nat) := [(1863852032,95539347895557,95539725436206),(1863910400,95539766510376,95540144051304),(1863968768,95540182091933,95540559633145)]
theorem point_links_checked14190 : (cuts14190.take 3).map (fun c => (1863843841-1+2*2^9*c.k,95539293075964+c.lower,95539670616575+c.upper)) = pointBounds14190 := by
 decide +kernel
def cuts14191 : List PrefixCut := [⟨51,370568111,370568361⟩,
⟨108,790653728,790654270⟩,
⟨128,942255800,942256444⟩]
theorem checked14191 : checkPrefixCuts (2^48) 1863974913 9 Manual.Count131072.C014191.packed 128 cuts14191 = true := by
 decide +kernel
def pointBounds14191 : List (Nat × Nat × Nat) := [(1864027136,95540592073162,95540969614651),(1864085504,95541012158779,95541389700560)]
theorem point_links_checked14191 : (cuts14191.take 2).map (fun c => (1863974913-1+2*2^9*c.k,95540221505051+c.lower,95540599046290+c.upper)) = pointBounds14191 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000130
