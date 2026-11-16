import PlattAssemblyKernel
import PlattCertificates.Count131072.C030224
import PlattCertificates.Count131072.C030225
import PlattCertificates.Count131072.C030226
import PlattCertificates.Count131072.C030227
import PlattCertificates.Count131072.C030228
import PlattCertificates.Count131072.C030229
import PlattCertificates.Count131072.C030230
import PlattCertificates.Count131072.C030231
import PlattCertificates.Count131072.C030232
import PlattCertificates.Count131072.C030233
import PlattCertificates.Count131072.C030234
import PlattCertificates.Count131072.C030235
import PlattCertificates.Count131072.C030236
import PlattCertificates.Count131072.C030237
import PlattCertificates.Count131072.C030238
import PlattCertificates.Count131072.C030239
import PlattCertificates.Count131072.C030240
import PlattCertificates.Count131072.C030241
import PlattCertificates.Count131072.C030242
import PlattCertificates.Count131072.C030243
import PlattCertificates.Count131072.C030244
import PlattCertificates.Count131072.C030245
import PlattCertificates.Count131072.C030246
import PlattCertificates.Count131072.C030247
import PlattCertificates.Count131072.C030248
import PlattCertificates.Count131072.C030249
import PlattCertificates.Count131072.C030250
import PlattCertificates.Count131072.C030251
import PlattCertificates.Count131072.C030252
import PlattCertificates.Count131072.C030253
import PlattCertificates.Count131072.C030254
import PlattCertificates.Count131072.C030255
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000007
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts30224 : List PrefixCut := [⟨13,45712193,45712220⟩,
⟨128,424606060,424606298⟩]
theorem checked30224 : checkPrefixCuts (2^48) 3965452289 9 Manual.Count131072.C030224.packed 128 cuts30224 = true := by
 decide +kernel
def pointBounds30224 : List (Nat × Nat × Nat) := [(3965465600,105322722818591,105323106193131)]
theorem point_links_checked30224 : (cuts30224.take 1).map (fun c => (3965452289-1+2*2^9*c.k,105322677106398+c.lower,105323060480911+c.upper)) = pointBounds30224 := by
 decide +kernel
def cuts30225 : List PrefixCut := [⟨7,22571442,22571454⟩,
⟨128,419126637,419126867⟩]
theorem checked30225 : checkPrefixCuts (2^48) 3965583361 9 Manual.Count131072.C030225.packed 128 cuts30225 = true := by
 decide +kernel
def pointBounds30225 : List (Nat × Nat × Nat) := [(3965590528,105323124283900,105323507658663)]
theorem point_links_checked30225 : (cuts30225.take 1).map (fun c => (3965583361-1+2*2^9*c.k,105323101712458+c.lower,105323485087209+c.upper)) = pointBounds30225 := by
 decide +kernel
def cuts30226 : List PrefixCut := [⟨1,2910061,2910062⟩,
⟨123,399026897,399027115⟩,
⟨128,414854278,414854505⟩]
theorem checked30226 : checkPrefixCuts (2^48) 3965714433 9 Manual.Count131072.C030226.packed 128 cuts30226 = true := by
 decide +kernel
def pointBounds30226 : List (Nat × Nat × Nat) := [(3965715456,105323523749156,105323907124138),(3965840384,105323919865992,105324303241191)]
theorem point_links_checked30226 : (cuts30226.take 2).map (fun c => (3965714433-1+2*2^9*c.k,105323520839095+c.lower,105323904214076+c.upper)) = pointBounds30226 := by
 decide +kernel
def cuts30227 : List PrefixCut := [⟨117,385812884,385813097⟩,
⟨128,421795943,421796176⟩]
theorem checked30227 : checkPrefixCuts (2^48) 3965845505 9 Manual.Count131072.C030227.packed 128 cuts30227 = true := by
 decide +kernel
def pointBounds30227 : List (Nat × Nat × Nat) := [(3965965312,105324321506257,105324704881678)]
theorem point_links_checked30227 : (cuts30227.take 1).map (fun c => (3965845505-1+2*2^9*c.k,105323935693373+c.lower,105324319068581+c.upper)) = pointBounds30227 := by
 decide +kernel
def cuts30228 : List PrefixCut := [⟨111,362450905,362451109⟩,
⟨128,418304466,418304700⟩]
theorem checked30228 : checkPrefixCuts (2^48) 3965976577 9 Manual.Count131072.C030228.packed 128 cuts30228 = true := by
 decide +kernel
def pointBounds30228 : List (Nat × Nat × Nat) := [(3966090240,105324719940221,105325103315866)]
theorem point_links_checked30228 : (cuts30228.take 1).map (fun c => (3965976577-1+2*2^9*c.k,105324357489316+c.lower,105324740864757+c.upper)) = pointBounds30228 := by
 decide +kernel
def cuts30229 : List PrefixCut := [⟨105,349238957,349239148⟩,
⟨128,425032694,425032929⟩]
theorem checked30229 : checkPrefixCuts (2^48) 3966107649 9 Manual.Count131072.C030229.packed 128 cuts30229 = true := by
 decide +kernel
def pointBounds30229 : List (Nat × Nat × Nat) := [(3966215168,105325125032739,105325508408605)]
theorem point_links_checked30229 : (cuts30229.take 1).map (fun c => (3966107649-1+2*2^9*c.k,105324775793782+c.lower,105325159169457+c.upper)) = pointBounds30229 := by
 decide +kernel
def cuts30230 : List PrefixCut := [⟨99,322969957,322970143⟩,
⟨128,418418733,418418976⟩]
theorem checked30230 : checkPrefixCuts (2^48) 3966238721 9 Manual.Count131072.C030230.packed 128 cuts30230 = true := by
 decide +kernel
def pointBounds30230 : List (Nat × Nat × Nat) := [(3966340096,105325523796433,105325907172529)]
theorem point_links_checked30230 : (cuts30230.take 1).map (fun c => (3966238721-1+2*2^9*c.k,105325200826476+c.lower,105325584202386+c.upper)) = pointBounds30230 := by
 decide +kernel
def cuts30231 : List PrefixCut := [⟨93,310824588,310824767⟩,
⟨128,426281941,426282185⟩]
theorem checked30231 : checkPrefixCuts (2^48) 3966369793 9 Manual.Count131072.C030231.packed 128 cuts30231 = true := by
 decide +kernel
def pointBounds30231 : List (Nat × Nat × Nat) := [(3966465024,105325930069797,105326313446129)]
theorem point_links_checked30231 : (cuts30231.take 1).map (fun c => (3966369793-1+2*2^9*c.k,105325619245209+c.lower,105326002621362+c.upper)) = pointBounds30231 := by
 decide +kernel
def cuts30232 : List PrefixCut := [⟨87,287042206,287042366⟩,
⟨128,422293977,422294211⟩]
theorem checked30232 : checkPrefixCuts (2^48) 3966500865 9 Manual.Count131072.C030232.packed 128 cuts30232 = true := by
 decide +kernel
def pointBounds30232 : List (Nat × Nat × Nat) := [(3966589952,105326332569356,105326715945913)]
theorem point_links_checked30232 : (cuts30232.take 1).map (fun c => (3966500865-1+2*2^9*c.k,105326045527150+c.lower,105326428903547+c.upper)) = pointBounds30232 := by
 decide +kernel
def cuts30233 : List PrefixCut := [⟨81,268157627,268157772⟩,
⟨128,419512667,419512896⟩]
theorem checked30233 : checkPrefixCuts (2^48) 3966631937 9 Manual.Count131072.C030233.packed 128 cuts30233 = true := by
 decide +kernel
def pointBounds30233 : List (Nat × Nat × Nat) := [(3966714880,105326735978754,105327119355530)]
theorem point_links_checked30233 : (cuts30233.take 1).map (fun c => (3966631937-1+2*2^9*c.k,105326467821127+c.lower,105326851197758+c.upper)) = pointBounds30233 := by
 decide +kernel
def cuts30234 : List PrefixCut := [⟨75,249912811,249912947⟩,
⟨128,425388171,425388403⟩]
theorem checked30234 : checkPrefixCuts (2^48) 3966763009 9 Manual.Count131072.C030234.packed 128 cuts30234 = true := by
 decide +kernel
def pointBounds30234 : List (Nat × Nat × Nat) := [(3966839808,105327137246605,105327520623601)]
theorem point_links_checked30234 : (cuts30234.take 1).map (fun c => (3966763009-1+2*2^9*c.k,105326887333794+c.lower,105327270710654+c.upper)) = pointBounds30234 := by
 decide +kernel
def cuts30235 : List PrefixCut := [⟨69,226134717,226134846⟩,
⟨128,418775328,418775569⟩]
theorem checked30235 : checkPrefixCuts (2^48) 3966894081 9 Manual.Count131072.C030235.packed 128 cuts30235 = true := by
 decide +kernel
def pointBounds30235 : List (Nat × Nat × Nat) := [(3966964736,105327538856682,105327922233903)]
theorem point_links_checked30235 : (cuts30235.take 1).map (fun c => (3966894081-1+2*2^9*c.k,105327312721965+c.lower,105327696099057+c.upper)) = pointBounds30235 := by
 decide +kernel
def cuts30236 : List PrefixCut := [⟨63,209666309,209666429⟩,
⟨128,425005295,425005536⟩]
theorem checked30236 : checkPrefixCuts (2^48) 3967025153 9 Manual.Count131072.C030236.packed 128 cuts30236 = true := by
 decide +kernel
def pointBounds30236 : List (Nat × Nat × Nat) := [(3967089664,105327941163602,105328324541055)]
theorem point_links_checked30236 : (cuts30236.take 1).map (fun c => (3967025153-1+2*2^9*c.k,105327731497293+c.lower,105328114874626+c.upper)) = pointBounds30236 := by
 decide +kernel
def cuts30237 : List PrefixCut := [⟨57,183265862,183265969⟩,
⟨128,414064938,414065176⟩]
theorem checked30237 : checkPrefixCuts (2^48) 3967156225 9 Manual.Count131072.C030237.packed 128 cuts30237 = true := by
 decide +kernel
def pointBounds30237 : List (Nat × Nat × Nat) := [(3967214592,105328339768450,105328723146131)]
theorem point_links_checked30237 : (cuts30237.take 1).map (fun c => (3967156225-1+2*2^9*c.k,105328156502588+c.lower,105328539880162+c.upper)) = pointBounds30237 := by
 decide +kernel
def cuts30238 : List PrefixCut := [⟨51,166232301,166232396⟩,
⟨128,417882440,417882677⟩]
theorem checked30238 : checkPrefixCuts (2^48) 3967287297 9 Manual.Count131072.C030238.packed 128 cuts30238 = true := by
 decide +kernel
def pointBounds30238 : List (Nat × Nat × Nat) := [(3967339520,105328736799827,105329120177734)]
theorem point_links_checked30238 : (cuts30238.take 1).map (fun c => (3967287297-1+2*2^9*c.k,105328570567526+c.lower,105328953945338+c.upper)) = pointBounds30238 := by
 decide +kernel
def cuts30239 : List PrefixCut := [⟨45,147142425,147142509⟩,
⟨128,415243688,415243920⟩]
theorem checked30239 : checkPrefixCuts (2^48) 3967418369 9 Manual.Count131072.C030239.packed 128 cuts30239 = true := by
 decide +kernel
def pointBounds30239 : List (Nat × Nat × Nat) := [(3967464448,105329135592391,105329518970524)]
theorem point_links_checked30239 : (cuts30239.take 1).map (fun c => (3967418369-1+2*2^9*c.k,105328988449966+c.lower,105329371828015+c.upper)) = pointBounds30239 := by
 decide +kernel
def cuts30240 : List PrefixCut := [⟨39,126847719,126847792⟩,
⟨128,424097806,424098045⟩]
theorem checked30240 : checkPrefixCuts (2^48) 3967549441 9 Manual.Count131072.C030240.packed 128 cuts30240 = true := by
 decide +kernel
def pointBounds30240 : List (Nat × Nat × Nat) := [(3967589376,105329530541373,105329913919727)]
theorem point_links_checked30240 : (cuts30240.take 1).map (fun c => (3967549441-1+2*2^9*c.k,105329403693654+c.lower,105329787071935+c.upper)) = pointBounds30240 := by
 decide +kernel
def cuts30241 : List PrefixCut := [⟨33,110952693,110952756⟩,
⟨128,421317176,421317415⟩]
theorem checked30241 : checkPrefixCuts (2^48) 3967680513 9 Manual.Count131072.C030241.packed 128 cuts30241 = true := by
 decide +kernel
def pointBounds30241 : List (Nat × Nat × Nat) := [(3967714304,105329938744153,105330322122736)]
theorem point_links_checked30241 : (cuts30241.take 1).map (fun c => (3967680513-1+2*2^9*c.k,105329827791460+c.lower,105330211169980+c.upper)) = pointBounds30241 := by
 decide +kernel
def cuts30242 : List PrefixCut := [⟨27,89738262,89738314⟩,
⟨128,418962292,418962532⟩]
theorem checked30242 : checkPrefixCuts (2^48) 3967811585 9 Manual.Count131072.C030242.packed 128 cuts30242 = true := by
 decide +kernel
def pointBounds30242 : List (Nat × Nat × Nat) := [(3967839232,105330338846898,105330722225709)]
theorem point_links_checked30242 : (cuts30242.take 1).map (fun c => (3967811585-1+2*2^9*c.k,105330249108636+c.lower,105330632487395+c.upper)) = pointBounds30242 := by
 decide +kernel
def cuts30243 : List PrefixCut := [⟨21,67673943,67673981⟩,
⟨128,416820338,416820580⟩]
theorem checked30243 : checkPrefixCuts (2^48) 3967942657 9 Manual.Count131072.C030243.packed 128 cuts30243 = true := by
 decide +kernel
def pointBounds30243 : List (Nat × Nat × Nat) := [(3967964160,105330735744871,105331119123908)]
theorem point_links_checked30243 : (cuts30243.take 1).map (fun c => (3967942657-1+2*2^9*c.k,105330668070928+c.lower,105331051449927+c.upper)) = pointBounds30243 := by
 decide +kernel
def cuts30244 : List PrefixCut := [⟨15,50434613,50434642⟩,
⟨128,419218346,419218583⟩]
theorem checked30244 : checkPrefixCuts (2^48) 3968073729 9 Manual.Count131072.C030244.packed 128 cuts30244 = true := by
 decide +kernel
def pointBounds30244 : List (Nat × Nat × Nat) := [(3968089088,105331135325879,105331518705149)]
theorem point_links_checked30244 : (cuts30244.take 1).map (fun c => (3968073729-1+2*2^9*c.k,105331084891266+c.lower,105331468270507+c.upper)) = pointBounds30244 := by
 decide +kernel
def cuts30245 : List PrefixCut := [⟨9,29933504,29933521⟩,
⟨128,426155710,426155945⟩]
theorem checked30245 : checkPrefixCuts (2^48) 3968204801 9 Manual.Count131072.C030245.packed 128 cuts30245 = true := by
 decide +kernel
def pointBounds30245 : List (Nat × Nat × Nat) := [(3968214016,105331534043116,105331917422611)]
theorem point_links_checked30245 : (cuts30245.take 1).map (fun c => (3968204801-1+2*2^9*c.k,105331504109612+c.lower,105331887489090+c.upper)) = pointBounds30245 := by
 decide +kernel
def cuts30246 : List PrefixCut := [⟨3,9717435,9717440⟩,
⟨125,406778177,406778407⟩,
⟨128,417062722,417062958⟩]
theorem checked30246 : checkPrefixCuts (2^48) 3968335873 9 Manual.Count131072.C030246.packed 128 cuts30246 = true := by
 decide +kernel
def pointBounds30246 : List (Nat × Nat × Nat) := [(3968338944,105331939982757,105332323362475),(3968463872,105332337043499,105332720423442)]
theorem point_links_checked30246 : (cuts30246.take 2).map (fun c => (3968335873-1+2*2^9*c.k,105331930265322+c.lower,105332313645035+c.upper)) = pointBounds30246 := by
 decide +kernel
def cuts30247 : List PrefixCut := [⟨119,389671711,389671927⟩,
⟨128,420666201,420666435⟩]
theorem checked30247 : checkPrefixCuts (2^48) 3968466945 9 Manual.Count131072.C030247.packed 128 cuts30247 = true := by
 decide +kernel
def pointBounds30247 : List (Nat × Nat × Nat) := [(3968588800,105332736999755,105333120379920)]
theorem point_links_checked30247 : (cuts30247.take 1).map (fun c => (3968466945-1+2*2^9*c.k,105332347328044+c.lower,105332730707993+c.upper)) = pointBounds30247 := by
 decide +kernel
def cuts30248 : List PrefixCut := [⟨113,366254038,366254239⟩,
⟨128,417531601,417531830⟩]
theorem checked30248 : checkPrefixCuts (2^48) 3968598017 9 Manual.Count131072.C030248.packed 128 cuts30248 = true := by
 decide +kernel
def pointBounds30248 : List (Nat × Nat × Nat) := [(3968713728,105333134248283,105333517628667)]
theorem point_links_checked30248 : (cuts30248.take 1).map (fun c => (3968598017-1+2*2^9*c.k,105332767994245+c.lower,105333151374428+c.upper)) = pointBounds30248 := by
 decide +kernel
def cuts30249 : List PrefixCut := [⟨107,347944310,347944504⟩,
⟨128,418085209,418085441⟩]
theorem checked30249 : checkPrefixCuts (2^48) 3968729089 9 Manual.Count131072.C030249.packed 128 cuts30249 = true := by
 decide +kernel
def pointBounds30249 : List (Nat × Nat × Nat) := [(3968838656,105333533470156,105333916850762)]
theorem point_links_checked30249 : (cuts30249.take 1).map (fun c => (3968729089-1+2*2^9*c.k,105333185525846+c.lower,105333568906258+c.upper)) = pointBounds30249 := by
 decide +kernel
def cuts30250 : List PrefixCut := [⟨101,332472573,332472762⟩,
⟨128,421546519,421546758⟩]
theorem checked30250 : checkPrefixCuts (2^48) 3968860161 9 Manual.Count131072.C030250.packed 128 cuts30250 = true := by
 decide +kernel
def pointBounds30250 : List (Nat × Nat × Nat) := [(3968963584,105333936083628,105334319464461)]
theorem point_links_checked30250 : (cuts30250.take 1).map (fun c => (3968860161-1+2*2^9*c.k,105333603611055+c.lower,105333986991699+c.upper)) = pointBounds30250 := by
 decide +kernel
def cuts30251 : List PrefixCut := [⟨95,310902868,310903046⟩,
⟨128,421177958,421178197⟩]
theorem checked30251 : checkPrefixCuts (2^48) 3968991233 9 Manual.Count131072.C030251.packed 128 cuts30251 = true := by
 decide +kernel
def pointBounds30251 : List (Nat × Nat × Nat) := [(3969088512,105334336060442,105334719441503)]
theorem point_links_checked30251 : (cuts30251.take 1).map (fun c => (3968991233-1+2*2^9*c.k,105334025157574+c.lower,105334408538457+c.upper)) = pointBounds30251 := by
 decide +kernel
def cuts30252 : List PrefixCut := [⟨89,293589495,293589660⟩,
⟨128,421376828,421377065⟩]
theorem checked30252 : checkPrefixCuts (2^48) 3969122305 9 Manual.Count131072.C030252.packed 128 cuts30252 = true := by
 decide +kernel
def pointBounds30252 : List (Nat × Nat × Nat) := [(3969213440,105334739925027,105335123306314)]
theorem point_links_checked30252 : (cuts30252.take 1).map (fun c => (3969122305-1+2*2^9*c.k,105334446335532+c.lower,105334829716654+c.upper)) = pointBounds30252 := by
 decide +kernel
def cuts30253 : List PrefixCut := [⟨83,274646239,274646395⟩,
⟨128,421150200,421150441⟩]
theorem checked30253 : checkPrefixCuts (2^48) 3969253377 9 Manual.Count131072.C030253.packed 128 cuts30253 = true := by
 decide +kernel
def pointBounds30253 : List (Nat × Nat × Nat) := [(3969338368,105335142358599,105335525740114)]
theorem point_links_checked30253 : (cuts30253.take 1).map (fun c => (3969253377-1+2*2^9*c.k,105334867712360+c.lower,105335251093719+c.upper)) = pointBounds30253 := by
 decide +kernel
def cuts30254 : List PrefixCut := [⟨77,254569683,254569825⟩,
⟨128,420356319,420356554⟩]
theorem checked30254 : checkPrefixCuts (2^48) 3969384449 9 Manual.Count131072.C030254.packed 128 cuts30254 = true := by
 decide +kernel
def pointBounds30254 : List (Nat × Nat × Nat) := [(3969463296,105335543432243,105335926813985)]
theorem point_links_checked30254 : (cuts30254.take 1).map (fun c => (3969384449-1+2*2^9*c.k,105335288862560+c.lower,105335672244160+c.upper)) = pointBounds30254 := by
 decide +kernel
def cuts30255 : List PrefixCut := [⟨71,235203433,235203568⟩,
⟨128,419775181,419775420⟩]
theorem checked30255 : checkPrefixCuts (2^48) 3969515521 9 Manual.Count131072.C030255.packed 128 cuts30255 = true := by
 decide +kernel
def pointBounds30255 : List (Nat × Nat × Nat) := [(3969588224,105335944422312,105336327804282)]
theorem point_links_checked30255 : (cuts30255.take 1).map (fun c => (3969515521-1+2*2^9*c.k,105335709218879+c.lower,105336092600714+c.upper)) = pointBounds30255 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000007
