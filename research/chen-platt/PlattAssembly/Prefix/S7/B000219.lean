import PlattAssemblyKernel
import PlattCertificates.Count131072.C067008
import PlattCertificates.Count131072.C067009
import PlattCertificates.Count131072.C067010
import PlattCertificates.Count131072.C067011
import PlattCertificates.Count131072.C067012
import PlattCertificates.Count131072.C067013
import PlattCertificates.Count131072.C067014
import PlattCertificates.Count131072.C067015
import PlattCertificates.Count131072.C067016
import PlattCertificates.Count131072.C067017
import PlattCertificates.Count131072.C067018
import PlattCertificates.Count131072.C067019
import PlattCertificates.Count131072.C067020
import PlattCertificates.Count131072.C067021
import PlattCertificates.Count131072.C067022
import PlattCertificates.Count131072.C067023
import PlattCertificates.Count131072.C067024
import PlattCertificates.Count131072.C067025
import PlattCertificates.Count131072.C067026
import PlattCertificates.Count131072.C067027
import PlattCertificates.Count131072.C067028
import PlattCertificates.Count131072.C067029
import PlattCertificates.Count131072.C067030
import PlattCertificates.Count131072.C067031
import PlattCertificates.Count131072.C067032
import PlattCertificates.Count131072.C067033
import PlattCertificates.Count131072.C067034
import PlattCertificates.Count131072.C067035
import PlattCertificates.Count131072.C067036
import PlattCertificates.Count131072.C067037
import PlattCertificates.Count131072.C067038
import PlattCertificates.Count131072.C067039
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000219
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts67008 : List PrefixCut := [⟨1,2562705,2562707⟩,
⟨64,184129016,184129124⟩]
theorem checked67008 : checkPrefixCuts (2^48) 8786804737 10 Manual.Count131072.C067008.packed 64 cuts67008 = true := by
 decide +kernel
def pointBounds67008 : List (Nat × Nat × Nat) := [(8786806784,115277495035520,115277884226704)]
theorem point_links_checked67008 : (cuts67008.take 1).map (fun c => (8786804737-1+2*2^10*c.k,115277492472815+c.lower,115277881663997+c.upper)) = pointBounds67008 := by
 decide +kernel
def cuts67009 : List PrefixCut := [⟨64,183325445,183325550⟩]
theorem checked67009 : checkPrefixCuts (2^48) 8786935809 10 Manual.Count131072.C067009.packed 64 cuts67009 = true := by
 decide +kernel
def cuts67010 : List PrefixCut := [⟨8,22583146,22583160⟩,
⟨64,181817146,181817256⟩]
theorem checked67010 : checkPrefixCuts (2^48) 8787066881 10 Manual.Count131072.C067010.packed 64 cuts67010 = true := by
 decide +kernel
def pointBounds67010 : List (Nat × Nat × Nat) := [(8787083264,115277882510422,115278271701831)]
theorem point_links_checked67010 : (cuts67010.take 1).map (fun c => (8787066881-1+2*2^10*c.k,115277859927276+c.lower,115278249118671+c.upper)) = pointBounds67010 := by
 decide +kernel
def cuts67011 : List PrefixCut := [⟨64,181910540,181910640⟩]
theorem checked67011 : checkPrefixCuts (2^48) 8787197953 10 Manual.Count131072.C067011.packed 64 cuts67011 = true := by
 decide +kernel
def cuts67012 : List PrefixCut := [⟨15,43851603,43851628⟩,
⟨64,184822720,184822827⟩]
theorem checked67012 : checkPrefixCuts (2^48) 8787329025 10 Manual.Count131072.C067012.packed 64 cuts67012 = true := by
 decide +kernel
def pointBounds67012 : List (Nat × Nat × Nat) := [(8787359744,115278267506565,115278656698195)]
theorem point_links_checked67012 : (cuts67012.take 1).map (fun c => (8787329025-1+2*2^10*c.k,115278223654962+c.lower,115278612846567+c.upper)) = pointBounds67012 := by
 decide +kernel
def cuts67013 : List PrefixCut := [⟨64,180687936,180688045⟩]
theorem checked67013 : checkPrefixCuts (2^48) 8787460097 10 Manual.Count131072.C067013.packed 64 cuts67013 = true := by
 decide +kernel
def cuts67014 : List PrefixCut := [⟨22,62332071,62332106⟩,
⟨64,182703174,182703279⟩]
theorem checked67014 : checkPrefixCuts (2^48) 8787591169 10 Manual.Count131072.C067014.packed 64 cuts67014 = true := by
 decide +kernel
def pointBounds67014 : List (Nat × Nat × Nat) := [(8787636224,115278651497689,115279040689545)]
theorem point_links_checked67014 : (cuts67014.take 1).map (fun c => (8787591169-1+2*2^10*c.k,115278589165618+c.lower,115278978357439+c.upper)) = pointBounds67014 := by
 decide +kernel
def cuts67015 : List PrefixCut := [⟨64,182828573,182828677⟩]
theorem checked67015 : checkPrefixCuts (2^48) 8787722241 10 Manual.Count131072.C067015.packed 64 cuts67015 = true := by
 decide +kernel
def cuts67016 : List PrefixCut := [⟨29,83662062,83662113⟩,
⟨64,183722681,183722786⟩]
theorem checked67016 : checkPrefixCuts (2^48) 8787853313 10 Manual.Count131072.C067016.packed 64 cuts67016 = true := by
 decide +kernel
def pointBounds67016 : List (Nat × Nat × Nat) := [(8787912704,115279038359427,115279427551508)]
theorem point_links_checked67016 : (cuts67016.take 1).map (fun c => (8787853313-1+2*2^10*c.k,115278954697365+c.lower,115279343889395+c.upper)) = pointBounds67016 := by
 decide +kernel
def cuts67017 : List PrefixCut := [⟨64,181317740,181317850⟩]
theorem checked67017 : checkPrefixCuts (2^48) 8787984385 10 Manual.Count131072.C067017.packed 64 cuts67017 = true := by
 decide +kernel
def cuts67018 : List PrefixCut := [⟨36,105567277,105567331⟩,
⟨64,186087346,186087446⟩]
theorem checked67018 : checkPrefixCuts (2^48) 8788115457 10 Manual.Count131072.C067018.packed 64 cuts67018 = true := by
 decide +kernel
def pointBounds67018 : List (Nat × Nat × Nat) := [(8788189184,115279425305063,115279814497362)]
theorem point_links_checked67018 : (cuts67018.take 1).map (fun c => (8788115457-1+2*2^10*c.k,115279319737786+c.lower,115279708930031+c.upper)) = pointBounds67018 := by
 decide +kernel
def cuts67019 : List PrefixCut := [⟨64,184643286,184643392⟩]
theorem checked67019 : checkPrefixCuts (2^48) 8788246529 10 Manual.Count131072.C067019.packed 64 cuts67019 = true := by
 decide +kernel
def cuts67020 : List PrefixCut := [⟨43,123339540,123339608⟩,
⟨64,183967944,183968048⟩]
theorem checked67020 : checkPrefixCuts (2^48) 8788377601 10 Manual.Count131072.C067020.packed 64 cuts67020 = true := by
 decide +kernel
def pointBounds67020 : List (Nat × Nat × Nat) := [(8788465664,115279813807958,115280203000477)]
theorem point_links_checked67020 : (cuts67020.take 1).map (fun c => (8788377601-1+2*2^10*c.k,115279690468418+c.lower,115280079660869+c.upper)) = pointBounds67020 := by
 decide +kernel
def cuts67021 : List PrefixCut := [⟨64,183420727,183420832⟩]
theorem checked67021 : checkPrefixCuts (2^48) 8788508673 10 Manual.Count131072.C067021.packed 64 cuts67021 = true := by
 decide +kernel
def cuts67022 : List PrefixCut := [⟨50,142712053,142712140⟩,
⟨64,182489220,182489331⟩]
theorem checked67022 : checkPrefixCuts (2^48) 8788639745 10 Manual.Count131072.C067022.packed 64 cuts67022 = true := by
 decide +kernel
def pointBounds67022 : List (Nat × Nat × Nat) := [(8788742144,115280200569142,115280589761889)]
theorem point_links_checked67022 : (cuts67022.take 1).map (fun c => (8788639745-1+2*2^10*c.k,115280057857089+c.lower,115280447049749+c.upper)) = pointBounds67022 := by
 decide +kernel
def cuts67023 : List PrefixCut := [⟨64,184311989,184312100⟩]
theorem checked67023 : checkPrefixCuts (2^48) 8788770817 10 Manual.Count131072.C067023.packed 64 cuts67023 = true := by
 decide +kernel
def cuts67024 : List PrefixCut := [⟨57,163172275,163172368⟩,
⟨64,183156326,183156432⟩]
theorem checked67024 : checkPrefixCuts (2^48) 8788901889 10 Manual.Count131072.C067024.packed 64 cuts67024 = true := by
 decide +kernel
def pointBounds67024 : List (Nat × Nat × Nat) := [(8789018624,115280587830573,115280977023548)]
theorem point_links_checked67024 : (cuts67024.take 1).map (fun c => (8788901889-1+2*2^10*c.k,115280424658298+c.lower,115280813851180+c.upper)) = pointBounds67024 := by
 decide +kernel
def cuts67025 : List PrefixCut := [⟨64,181904601,181904704⟩]
theorem checked67025 : checkPrefixCuts (2^48) 8789032961 10 Manual.Count131072.C067025.packed 64 cuts67025 = true := by
 decide +kernel
def cuts67026 : List PrefixCut := [⟨64,183823386,183823489⟩]
theorem checked67026 : checkPrefixCuts (2^48) 8789164033 10 Manual.Count131072.C067026.packed 64 cuts67026 = true := by
 decide +kernel
def pointBounds67026 : List (Nat × Nat × Nat) := [(8789295104,115280973542611,115281362735805)]
theorem point_links_checked67026 : (cuts67026.take 1).map (fun c => (8789164033-1+2*2^10*c.k,115280789719225+c.lower,115281178912316+c.upper)) = pointBounds67026 := by
 decide +kernel
def cuts67027 : List PrefixCut := [⟨64,182763829,182763933⟩]
theorem checked67027 : checkPrefixCuts (2^48) 8789295105 10 Manual.Count131072.C067027.packed 64 cuts67027 = true := by
 decide +kernel
def cuts67028 : List PrefixCut := [⟨64,183113378,183113478⟩]
theorem checked67028 : checkPrefixCuts (2^48) 8789426177 10 Manual.Count131072.C067028.packed 64 cuts67028 = true := by
 decide +kernel
def cuts67029 : List PrefixCut := [⟨7,20206993,20207003⟩,
⟨64,182886479,182886589⟩]
theorem checked67029 : checkPrefixCuts (2^48) 8789557249 10 Manual.Count131072.C067029.packed 64 cuts67029 = true := by
 decide +kernel
def pointBounds67029 : List (Nat × Nat × Nat) := [(8789571584,115281359626811,115281748820219)]
theorem point_links_checked67029 : (cuts67029.take 1).map (fun c => (8789557249-1+2*2^10*c.k,115281339419818+c.lower,115281728613216+c.upper)) = pointBounds67029 := by
 decide +kernel
def cuts67030 : List PrefixCut := [⟨64,184741086,184741198⟩]
theorem checked67030 : checkPrefixCuts (2^48) 8789688321 10 Manual.Count131072.C067030.packed 64 cuts67030 = true := by
 decide +kernel
def cuts67031 : List PrefixCut := [⟨14,39740266,39740289⟩,
⟨64,181247868,181247973⟩]
theorem checked67031 : checkPrefixCuts (2^48) 8789819393 10 Manual.Count131072.C067031.packed 64 cuts67031 = true := by
 decide +kernel
def pointBounds67031 : List (Nat × Nat × Nat) := [(8789848064,115281746787649,115282135981292)]
theorem point_links_checked67031 : (cuts67031.take 1).map (fun c => (8789819393-1+2*2^10*c.k,115281707047383+c.lower,115282096241003+c.upper)) = pointBounds67031 := by
 decide +kernel
def cuts67032 : List PrefixCut := [⟨64,182814259,182814360⟩]
theorem checked67032 : checkPrefixCuts (2^48) 8789950465 10 Manual.Count131072.C067032.packed 64 cuts67032 = true := by
 decide +kernel
def cuts67033 : List PrefixCut := [⟨21,59464480,59464515⟩,
⟨64,184060365,184060472⟩]
theorem checked67033 : checkPrefixCuts (2^48) 8790081537 10 Manual.Count131072.C067033.packed 64 cuts67033 = true := by
 decide +kernel
def pointBounds67033 : List (Nat × Nat × Nat) := [(8790124544,115282130573990,115282519767851)]
theorem point_links_checked67033 : (cuts67033.take 1).map (fun c => (8790081537-1+2*2^10*c.k,115282071109510+c.lower,115282460303336+c.upper)) = pointBounds67033 := by
 decide +kernel
def cuts67034 : List PrefixCut := [⟨64,184794106,184794211⟩]
theorem checked67034 : checkPrefixCuts (2^48) 8790212609 10 Manual.Count131072.C067034.packed 64 cuts67034 = true := by
 decide +kernel
def cuts67035 : List PrefixCut := [⟨28,81396917,81396969⟩,
⟨64,184279026,184279141⟩]
theorem checked67035 : checkPrefixCuts (2^48) 8790343681 10 Manual.Count131072.C067035.packed 64 cuts67035 = true := by
 decide +kernel
def pointBounds67035 : List (Nat × Nat × Nat) := [(8790401024,115282521360898,115282910554988)]
theorem point_links_checked67035 : (cuts67035.take 1).map (fun c => (8790343681-1+2*2^10*c.k,115282439963981+c.lower,115282829158019+c.upper)) = pointBounds67035 := by
 decide +kernel
def cuts67036 : List PrefixCut := [⟨64,181714655,181714762⟩]
theorem checked67036 : checkPrefixCuts (2^48) 8790474753 10 Manual.Count131072.C067036.packed 64 cuts67036 = true := by
 decide +kernel
def cuts67037 : List PrefixCut := [⟨35,100382180,100382238⟩,
⟨64,185426230,185426333⟩]
theorem checked67037 : checkPrefixCuts (2^48) 8790605825 10 Manual.Count131072.C067037.packed 64 cuts67037 = true := by
 decide +kernel
def pointBounds67037 : List (Nat × Nat × Nat) := [(8790677504,115282906339842,115283295534160)]
theorem point_links_checked67037 : (cuts67037.take 1).map (fun c => (8790605825-1+2*2^10*c.k,115282805957662+c.lower,115283195151922+c.upper)) = pointBounds67037 := by
 decide +kernel
def cuts67038 : List PrefixCut := [⟨64,183982600,183982709⟩]
theorem checked67038 : checkPrefixCuts (2^48) 8790736897 10 Manual.Count131072.C067038.packed 64 cuts67038 = true := by
 decide +kernel
def cuts67039 : List PrefixCut := [⟨42,118469756,118469831⟩,
⟨64,181770555,181770669⟩]
theorem checked67039 : checkPrefixCuts (2^48) 8790867969 10 Manual.Count131072.C067039.packed 64 cuts67039 = true := by
 decide +kernel
def pointBounds67039 : List (Nat × Nat × Nat) := [(8790953984,115283293836248,115283683030795)]
theorem point_links_checked67039 : (cuts67039.take 1).map (fun c => (8790867969-1+2*2^10*c.k,115283175366492+c.lower,115283564560964+c.upper)) = pointBounds67039 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000219
