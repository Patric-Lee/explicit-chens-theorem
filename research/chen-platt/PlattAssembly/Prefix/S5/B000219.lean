import PlattAssemblyKernel
import PlattCertificates.Count131072.C047008
import PlattCertificates.Count131072.C047009
import PlattCertificates.Count131072.C047010
import PlattCertificates.Count131072.C047011
import PlattCertificates.Count131072.C047012
import PlattCertificates.Count131072.C047013
import PlattCertificates.Count131072.C047014
import PlattCertificates.Count131072.C047015
import PlattCertificates.Count131072.C047016
import PlattCertificates.Count131072.C047017
import PlattCertificates.Count131072.C047018
import PlattCertificates.Count131072.C047019
import PlattCertificates.Count131072.C047020
import PlattCertificates.Count131072.C047021
import PlattCertificates.Count131072.C047022
import PlattCertificates.Count131072.C047023
import PlattCertificates.Count131072.C047024
import PlattCertificates.Count131072.C047025
import PlattCertificates.Count131072.C047026
import PlattCertificates.Count131072.C047027
import PlattCertificates.Count131072.C047028
import PlattCertificates.Count131072.C047029
import PlattCertificates.Count131072.C047030
import PlattCertificates.Count131072.C047031
import PlattCertificates.Count131072.C047032
import PlattCertificates.Count131072.C047033
import PlattCertificates.Count131072.C047034
import PlattCertificates.Count131072.C047035
import PlattCertificates.Count131072.C047036
import PlattCertificates.Count131072.C047037
import PlattCertificates.Count131072.C047038
import PlattCertificates.Count131072.C047039
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000219
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts47008 : List PrefixCut := [⟨39,163623659,163623755⟩,
⟨64,267485227,267485381⟩]
theorem checked47008 : checkPrefixCuts (2^48) 6165364737 10 Manual.Count131072.C047008.packed 64 cuts47008 = true := by
 decide +kernel
def pointBounds47008 : List (Nat × Nat × Nat) := [(6165444608,110888089615266,110888476298066)]
theorem point_links_checked47008 : (cuts47008.take 1).map (fun c => (6165364737-1+2*2^10*c.k,110887925991607+c.lower,110888312674311+c.upper)) = pointBounds47008 := by
 decide +kernel
def cuts47009 : List PrefixCut := [⟨64,264466419,264466570⟩]
theorem checked47009 : checkPrefixCuts (2^48) 6165495809 10 Manual.Count131072.C047009.packed 64 cuts47009 = true := by
 decide +kernel
def cuts47010 : List PrefixCut := [⟨6,25656553,25656568⟩,
⟨64,265967347,265967503⟩]
theorem checked47010 : checkPrefixCuts (2^48) 6165626881 10 Manual.Count131072.C047010.packed 64 cuts47010 = true := by
 decide +kernel
def pointBounds47010 : List (Nat × Nat × Nat) := [(6165639168,110888483599806,110888870282830)]
theorem point_links_checked47010 : (cuts47010.take 1).map (fun c => (6165626881-1+2*2^10*c.k,110888457943253+c.lower,110888844626262+c.upper)) = pointBounds47010 := by
 decide +kernel
def cuts47011 : List PrefixCut := [⟨37,151013587,151013677⟩,
⟨64,262994355,262994510⟩]
theorem checked47011 : checkPrefixCuts (2^48) 6165757953 10 Manual.Count131072.C047011.packed 64 cuts47011 = true := by
 decide +kernel
def pointBounds47011 : List (Nat × Nat × Nat) := [(6165833728,110888874924187,110889261607442)]
theorem point_links_checked47011 : (cuts47011.take 1).map (fun c => (6165757953-1+2*2^10*c.k,110888723910600+c.lower,110889110593765+c.upper)) = pointBounds47011 := by
 decide +kernel
def cuts47012 : List PrefixCut := [⟨64,262988768,262988922⟩]
theorem checked47012 : checkPrefixCuts (2^48) 6165889025 10 Manual.Count131072.C047012.packed 64 cuts47012 = true := by
 decide +kernel
def cuts47013 : List PrefixCut := [⟨4,17438046,17438055⟩,
⟨64,268187151,268187304⟩]
theorem checked47013 : checkPrefixCuts (2^48) 6166020097 10 Manual.Count131072.C047013.packed 64 cuts47013 = true := by
 decide +kernel
def pointBounds47013 : List (Nat × Nat × Nat) := [(6166028288,110889267331769,110889654015252)]
theorem point_links_checked47013 : (cuts47013.take 1).map (fun c => (6166020097-1+2*2^10*c.k,110889249893723+c.lower,110889636577197+c.upper)) = pointBounds47013 := by
 decide +kernel
def cuts47014 : List PrefixCut := [⟨35,145937063,145937149⟩,
⟨64,266720728,266720892⟩]
theorem checked47014 : checkPrefixCuts (2^48) 6166151169 10 Manual.Count131072.C047014.packed 64 cuts47014 = true := by
 decide +kernel
def pointBounds47014 : List (Nat × Nat × Nat) := [(6166222848,110889664017937,110890050701650)]
theorem point_links_checked47014 : (cuts47014.take 1).map (fun c => (6166151169-1+2*2^10*c.k,110889518080874+c.lower,110889904764501+c.upper)) = pointBounds47014 := by
 decide +kernel
def cuts47015 : List PrefixCut := [⟨64,266806356,266806507⟩]
theorem checked47015 : checkPrefixCuts (2^48) 6166282241 10 Manual.Count131072.C047015.packed 64 cuts47015 = true := by
 decide +kernel
def cuts47016 : List PrefixCut := [⟨2,8444591,8444596⟩,
⟨64,264153224,264153379⟩]
theorem checked47016 : checkPrefixCuts (2^48) 6166413313 10 Manual.Count131072.C047016.packed 64 cuts47016 = true := by
 decide +kernel
def pointBounds47016 : List (Nat × Nat × Nat) := [(6166417408,110890060052549,110890446736496)]
theorem point_links_checked47016 : (cuts47016.take 1).map (fun c => (6166413313-1+2*2^10*c.k,110890051607958+c.lower,110890438291900+c.upper)) = pointBounds47016 := by
 decide +kernel
def cuts47017 : List PrefixCut := [⟨33,137802958,137803033⟩,
⟨64,264649706,264649857⟩]
theorem checked47017 : checkPrefixCuts (2^48) 6166544385 10 Manual.Count131072.C047017.packed 64 cuts47017 = true := by
 decide +kernel
def pointBounds47017 : List (Nat × Nat × Nat) := [(6166611968,110890453564140,110890840248312)]
theorem point_links_checked47017 : (cuts47017.take 1).map (fun c => (6166544385-1+2*2^10*c.k,110890315761182+c.lower,110890702445279+c.upper)) = pointBounds47017 := by
 decide +kernel
def cuts47018 : List PrefixCut := [⟨64,267839151,267839302⟩]
theorem checked47018 : checkPrefixCuts (2^48) 6166675457 10 Manual.Count131072.C047018.packed 64 cuts47018 = true := by
 decide +kernel
def pointBounds47018 : List (Nat × Nat × Nat) := [(6166806528,110890848250039,110891234934438)]
theorem point_links_checked47018 : (cuts47018.take 1).map (fun c => (6166675457-1+2*2^10*c.k,110890580410888+c.lower,110890967095136+c.upper)) = pointBounds47018 := by
 decide +kernel
def cuts47019 : List PrefixCut := [⟨64,263816853,263817004⟩]
theorem checked47019 : checkPrefixCuts (2^48) 6166806529 10 Manual.Count131072.C047019.packed 64 cuts47019 = true := by
 decide +kernel
def cuts47020 : List PrefixCut := [⟨31,130765306,130765382⟩,
⟨64,265773903,265774060⟩]
theorem checked47020 : checkPrefixCuts (2^48) 6166937601 10 Manual.Count131072.C047020.packed 64 cuts47020 = true := by
 decide +kernel
def pointBounds47020 : List (Nat × Nat × Nat) := [(6167001088,110891242832198,110891629516824)]
theorem point_links_checked47020 : (cuts47020.take 1).map (fun c => (6166937601-1+2*2^10*c.k,110891112066892+c.lower,110891498751442+c.upper)) = pointBounds47020 := by
 decide +kernel
def cuts47021 : List PrefixCut := [⟨62,256411914,256412060⟩,
⟨64,264216465,264216615⟩]
theorem checked47021 : checkPrefixCuts (2^48) 6167068673 10 Manual.Count131072.C047021.packed 64 cuts47021 = true := by
 decide +kernel
def pointBounds47021 : List (Nat × Nat × Nat) := [(6167195648,110891634252709,110892020937562)]
theorem point_links_checked47021 : (cuts47021.take 1).map (fun c => (6167068673-1+2*2^10*c.k,110891377840795+c.lower,110891764525502+c.upper)) = pointBounds47021 := by
 decide +kernel
def cuts47022 : List PrefixCut := [⟨64,264393355,264393510⟩]
theorem checked47022 : checkPrefixCuts (2^48) 6167199745 10 Manual.Count131072.C047022.packed 64 cuts47022 = true := by
 decide +kernel
def cuts47023 : List PrefixCut := [⟨29,120031741,120031811⟩,
⟨64,264433405,264433556⟩]
theorem checked47023 : checkPrefixCuts (2^48) 6167330817 10 Manual.Count131072.C047023.packed 64 cuts47023 = true := by
 decide +kernel
def pointBounds47023 : List (Nat × Nat × Nat) := [(6167390208,110892026482356,110892413167438)]
theorem point_links_checked47023 : (cuts47023.take 1).map (fun c => (6167330817-1+2*2^10*c.k,110891906450615+c.lower,110892293135627+c.upper)) = pointBounds47023 := by
 decide +kernel
def cuts47024 : List PrefixCut := [⟨60,248135099,248135247⟩,
⟨64,264747241,264747399⟩]
theorem checked47024 : checkPrefixCuts (2^48) 6167461889 10 Manual.Count131072.C047024.packed 64 cuts47024 = true := by
 decide +kernel
def pointBounds47024 : List (Nat × Nat × Nat) := [(6167584768,110892419019119,110892805704430)]
theorem point_links_checked47024 : (cuts47024.take 1).map (fun c => (6167461889-1+2*2^10*c.k,110892170884020+c.lower,110892557569183+c.upper)) = pointBounds47024 := by
 decide +kernel
def cuts47025 : List PrefixCut := [⟨64,269716077,269716230⟩]
theorem checked47025 : checkPrefixCuts (2^48) 6167592961 10 Manual.Count131072.C047025.packed 64 cuts47025 = true := by
 decide +kernel
def cuts47026 : List PrefixCut := [⟨27,109527711,109527771⟩,
⟨64,261678347,261678495⟩]
theorem checked47026 : checkPrefixCuts (2^48) 6167724033 10 Manual.Count131072.C047026.packed 64 cuts47026 = true := by
 decide +kernel
def pointBounds47026 : List (Nat × Nat × Nat) := [(6167779328,110892814875049,110893201560583)]
theorem point_links_checked47026 : (cuts47026.take 1).map (fun c => (6167724033-1+2*2^10*c.k,110892705347338+c.lower,110893092032812+c.upper)) = pointBounds47026 := by
 decide +kernel
def cuts47027 : List PrefixCut := [⟨58,236984350,236984481⟩,
⟨64,261307729,261307873⟩]
theorem checked47027 : checkPrefixCuts (2^48) 6167855105 10 Manual.Count131072.C047027.packed 64 cuts47027 = true := by
 decide +kernel
def pointBounds47027 : List (Nat × Nat × Nat) := [(6167973888,110893204010035,110893590695788)]
theorem point_links_checked47027 : (cuts47027.take 1).map (fun c => (6167855105-1+2*2^10*c.k,110892967025685+c.lower,110893353711307+c.upper)) = pointBounds47027 := by
 decide +kernel
def cuts47028 : List PrefixCut := [⟨64,265409254,265409411⟩]
theorem checked47028 : checkPrefixCuts (2^48) 6167986177 10 Manual.Count131072.C047028.packed 64 cuts47028 = true := by
 decide +kernel
def cuts47029 : List PrefixCut := [⟨25,104272896,104272955⟩,
⟨64,266316280,266316431⟩]
theorem checked47029 : checkPrefixCuts (2^48) 6168117249 10 Manual.Count131072.C047029.packed 64 cuts47029 = true := by
 decide +kernel
def pointBounds47029 : List (Nat × Nat × Nat) := [(6168168448,110893598015564,110893984701546)]
theorem point_links_checked47029 : (cuts47029.take 1).map (fun c => (6168117249-1+2*2^10*c.k,110893493742668+c.lower,110893880428591+c.upper)) = pointBounds47029 := by
 decide +kernel
def cuts47030 : List PrefixCut := [⟨56,233775043,233775178⟩,
⟨64,266949481,266949636⟩]
theorem checked47030 : checkPrefixCuts (2^48) 6168248321 10 Manual.Count131072.C047030.packed 64 cuts47030 = true := by
 decide +kernel
def pointBounds47030 : List (Nat × Nat × Nat) := [(6168363008,110893993833991,110894380520200)]
theorem point_links_checked47030 : (cuts47030.take 1).map (fun c => (6168248321-1+2*2^10*c.k,110893760058948+c.lower,110894146745022+c.upper)) = pointBounds47030 := by
 decide +kernel
def cuts47031 : List PrefixCut := [⟨64,266670016,266670167⟩]
theorem checked47031 : checkPrefixCuts (2^48) 6168379393 10 Manual.Count131072.C047031.packed 64 cuts47031 = true := by
 decide +kernel
def cuts47032 : List PrefixCut := [⟨23,94775090,94775145⟩,
⟨64,264702233,264702386⟩]
theorem checked47032 : checkPrefixCuts (2^48) 6168510465 10 Manual.Count131072.C047032.packed 64 cuts47032 = true := by
 decide +kernel
def pointBounds47032 : List (Nat × Nat × Nat) := [(6168557568,110894388453535,110894775139970)]
theorem point_links_checked47032 : (cuts47032.take 1).map (fun c => (6168510465-1+2*2^10*c.k,110894293678445+c.lower,110894680364825+c.upper)) = pointBounds47032 := by
 decide +kernel
def cuts47033 : List PrefixCut := [⟨54,220390760,220390890⟩,
⟨64,259996792,259996949⟩]
theorem checked47033 : checkPrefixCuts (2^48) 6168641537 10 Manual.Count131072.C047033.packed 64 cuts47033 = true := by
 decide +kernel
def pointBounds47033 : List (Nat × Nat × Nat) := [(6168752128,110894778771438,110895165458101)]
theorem point_links_checked47033 : (cuts47033.take 1).map (fun c => (6168641537-1+2*2^10*c.k,110894558380678+c.lower,110894945067211+c.upper)) = pointBounds47033 := by
 decide +kernel
def cuts47034 : List PrefixCut := [⟨64,267291823,267291975⟩]
theorem checked47034 : checkPrefixCuts (2^48) 6168772609 10 Manual.Count131072.C047034.packed 64 cuts47034 = true := by
 decide +kernel
def cuts47035 : List PrefixCut := [⟨21,83225231,83225278⟩,
⟨64,264913466,264913612⟩]
theorem checked47035 : checkPrefixCuts (2^48) 6168903681 10 Manual.Count131072.C047035.packed 64 cuts47035 = true := by
 decide +kernel
def pointBounds47035 : List (Nat × Nat × Nat) := [(6168946688,110895168894524,110895555581413)]
theorem point_links_checked47035 : (cuts47035.take 1).map (fun c => (6168903681-1+2*2^10*c.k,110895085669293+c.lower,110895472356135+c.upper)) = pointBounds47035 := by
 decide +kernel
def cuts47036 : List PrefixCut := [⟨52,214627800,214627922⟩,
⟨64,262763418,262763568⟩]
theorem checked47036 : checkPrefixCuts (2^48) 6169034753 10 Manual.Count131072.C047036.packed 64 cuts47036 = true := by
 decide +kernel
def pointBounds47036 : List (Nat × Nat × Nat) := [(6169141248,110895565210559,110895951897669)]
theorem point_links_checked47036 : (cuts47036.take 1).map (fun c => (6169034753-1+2*2^10*c.k,110895350582759+c.lower,110895737269747+c.upper)) = pointBounds47036 := by
 decide +kernel
def cuts47037 : List PrefixCut := [⟨64,260659052,260659207⟩]
theorem checked47037 : checkPrefixCuts (2^48) 6169165825 10 Manual.Count131072.C047037.packed 64 cuts47037 = true := by
 decide +kernel
def cuts47038 : List PrefixCut := [⟨19,79934956,79935004⟩,
⟨64,268820335,268820485⟩]
theorem checked47038 : checkPrefixCuts (2^48) 6169296897 10 Manual.Count131072.C047038.packed 64 cuts47038 = true := by
 decide +kernel
def pointBounds47038 : List (Nat × Nat × Nat) := [(6169335808,110895953940185,110896340627526)]
theorem point_links_checked47038 : (cuts47038.take 1).map (fun c => (6169296897-1+2*2^10*c.k,110895874005229+c.lower,110896260692522+c.upper)) = pointBounds47038 := by
 decide +kernel
def cuts47039 : List PrefixCut := [⟨50,207998762,207998885⟩,
⟨64,264617261,264617412⟩]
theorem checked47039 : checkPrefixCuts (2^48) 6169427969 10 Manual.Count131072.C047039.packed 64 cuts47039 = true := by
 decide +kernel
def pointBounds47039 : List (Nat × Nat × Nat) := [(6169530368,110896350824326,110896737511892)]
theorem point_links_checked47039 : (cuts47039.take 1).map (fun c => (6169427969-1+2*2^10*c.k,110896142825564+c.lower,110896529513007+c.upper)) = pointBounds47039 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000219
