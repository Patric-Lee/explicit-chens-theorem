import PlattAssemblyKernel
import PlattCertificates.Count131072.C053328
import PlattCertificates.Count131072.C053329
import PlattCertificates.Count131072.C053330
import PlattCertificates.Count131072.C053331
import PlattCertificates.Count131072.C053332
import PlattCertificates.Count131072.C053333
import PlattCertificates.Count131072.C053334
import PlattCertificates.Count131072.C053335
import PlattCertificates.Count131072.C053336
import PlattCertificates.Count131072.C053337
import PlattCertificates.Count131072.C053338
import PlattCertificates.Count131072.C053339
import PlattCertificates.Count131072.C053340
import PlattCertificates.Count131072.C053341
import PlattCertificates.Count131072.C053342
import PlattCertificates.Count131072.C053343
import PlattCertificates.Count131072.C053344
import PlattCertificates.Count131072.C053345
import PlattCertificates.Count131072.C053346
import PlattCertificates.Count131072.C053347
import PlattCertificates.Count131072.C053348
import PlattCertificates.Count131072.C053349
import PlattCertificates.Count131072.C053350
import PlattCertificates.Count131072.C053351
import PlattCertificates.Count131072.C053352
import PlattCertificates.Count131072.C053353
import PlattCertificates.Count131072.C053354
import PlattCertificates.Count131072.C053355
import PlattCertificates.Count131072.C053356
import PlattCertificates.Count131072.C053357
import PlattCertificates.Count131072.C053358
import PlattCertificates.Count131072.C053359
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000104
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts53328 : List PrefixCut := [⟨42,153701171,153701257⟩,
⟨64,235601924,235602056⟩]
theorem checked53328 : checkPrefixCuts (2^48) 6993739777 10 Manual.Count131072.C053328.packed 64 cuts53328 = true := by
 decide +kernel
def pointBounds53328 : List (Nat × Nat × Nat) := [(6993825792,112457806207694,112458193785015)]
theorem point_links_checked53328 : (cuts53328.take 1).map (fun c => (6993739777-1+2*2^10*c.k,112457652506523+c.lower,112458040083758+c.upper)) = pointBounds53328 := by
 decide +kernel
def cuts53329 : List PrefixCut := [⟨64,234269422,234269552⟩]
theorem checked53329 : checkPrefixCuts (2^48) 6993870849 10 Manual.Count131072.C053329.packed 64 cuts53329 = true := by
 decide +kernel
def cuts53330 : List PrefixCut := [⟨21,78719343,78719386⟩,
⟨64,235713856,235713988⟩]
theorem checked53330 : checkPrefixCuts (2^48) 6994001921 10 Manual.Count131072.C053330.packed 64 cuts53330 = true := by
 decide +kernel
def pointBounds53330 : List (Nat × Nat × Nat) := [(6994044928,112458201097212,112458588674752)]
theorem point_links_checked53330 : (cuts53330.take 1).map (fun c => (6994001921-1+2*2^10*c.k,112458122377869+c.lower,112458509955366+c.upper)) = pointBounds53330 := by
 decide +kernel
def cuts53331 : List PrefixCut := [⟨64,231483782,231483914⟩]
theorem checked53331 : checkPrefixCuts (2^48) 6994132993 10 Manual.Count131072.C053331.packed 64 cuts53331 = true := by
 decide +kernel
def pointBounds53331 : List (Nat × Nat × Nat) := [(6994264064,112458589575507,112458977153268)]
theorem point_links_checked53331 : (cuts53331.take 1).map (fun c => (6994132993-1+2*2^10*c.k,112458358091725+c.lower,112458745669354+c.upper)) = pointBounds53331 := by
 decide +kernel
def cuts53332 : List PrefixCut := [⟨64,233934298,233934432⟩]
theorem checked53332 : checkPrefixCuts (2^48) 6994264065 10 Manual.Count131072.C053332.packed 64 cuts53332 = true := by
 decide +kernel
def cuts53333 : List PrefixCut := [⟨43,155376938,155377030⟩,
⟨64,231595840,231595974⟩]
theorem checked53333 : checkPrefixCuts (2^48) 6994395137 10 Manual.Count131072.C053333.packed 64 cuts53333 = true := by
 decide +kernel
def pointBounds53333 : List (Nat × Nat × Nat) := [(6994483200,112458978886743,112459366464730)]
theorem point_links_checked53333 : (cuts53333.take 1).map (fun c => (6994395137-1+2*2^10*c.k,112458823509805+c.lower,112459211087700+c.upper)) = pointBounds53333 := by
 decide +kernel
def cuts53334 : List PrefixCut := [⟨64,231189103,231189235⟩]
theorem checked53334 : checkPrefixCuts (2^48) 6994526209 10 Manual.Count131072.C053334.packed 64 cuts53334 = true := by
 decide +kernel
def cuts53335 : List PrefixCut := [⟨22,79677745,79677789⟩,
⟨64,232231010,232231143⟩]
theorem checked53335 : checkPrefixCuts (2^48) 6994657281 10 Manual.Count131072.C053335.packed 64 cuts53335 = true := by
 decide +kernel
def pointBounds53335 : List (Nat × Nat × Nat) := [(6994702336,112459365972493,112459753550698)]
theorem point_links_checked53335 : (cuts53335.take 1).map (fun c => (6994657281-1+2*2^10*c.k,112459286294748+c.lower,112459673872909+c.upper)) = pointBounds53335 := by
 decide +kernel
def cuts53336 : List PrefixCut := [⟨64,235808059,235808195⟩]
theorem checked53336 : checkPrefixCuts (2^48) 6994788353 10 Manual.Count131072.C053336.packed 64 cuts53336 = true := by
 decide +kernel
def cuts53337 : List PrefixCut := [⟨1,3178952,3178954⟩,
⟨64,231860159,231860291⟩]
theorem checked53337 : checkPrefixCuts (2^48) 6994919425 10 Manual.Count131072.C053337.packed 64 cuts53337 = true := by
 decide +kernel
def pointBounds53337 : List (Nat × Nat × Nat) := [(6994921472,112459757512769,112460145091201)]
theorem point_links_checked53337 : (cuts53337.take 1).map (fun c => (6994919425-1+2*2^10*c.k,112459754333817+c.lower,112460141912247+c.upper)) = pointBounds53337 := by
 decide +kernel
def cuts53338 : List PrefixCut := [⟨44,161760354,161760442⟩,
⟨64,233666577,233666705⟩]
theorem checked53338 : checkPrefixCuts (2^48) 6995050497 10 Manual.Count131072.C053338.packed 64 cuts53338 = true := by
 decide +kernel
def pointBounds53338 : List (Nat × Nat × Nat) := [(6995140608,112460147954330,112460535532980)]
theorem point_links_checked53338 : (cuts53338.take 1).map (fun c => (6995050497-1+2*2^10*c.k,112459986193976+c.lower,112460373772538+c.upper)) = pointBounds53338 := by
 decide +kernel
def cuts53339 : List PrefixCut := [⟨64,232173382,232173513⟩]
theorem checked53339 : checkPrefixCuts (2^48) 6995181569 10 Manual.Count131072.C053339.packed 64 cuts53339 = true := by
 decide +kernel
def cuts53340 : List PrefixCut := [⟨23,82325944,82325990⟩,
⟨64,230519299,230519427⟩]
theorem checked53340 : checkPrefixCuts (2^48) 6995312641 10 Manual.Count131072.C053340.packed 64 cuts53340 = true := by
 decide +kernel
def pointBounds53340 : List (Nat × Nat × Nat) := [(6995359744,112460534359879,112460921938746)]
theorem point_links_checked53340 : (cuts53340.take 1).map (fun c => (6995312641-1+2*2^10*c.k,112460452033935+c.lower,112460839612756+c.upper)) = pointBounds53340 := by
 decide +kernel
def cuts53341 : List PrefixCut := [⟨64,236389515,236389650⟩]
theorem checked53341 : checkPrefixCuts (2^48) 6995443713 10 Manual.Count131072.C053341.packed 64 cuts53341 = true := by
 decide +kernel
def cuts53342 : List PrefixCut := [⟨2,6880377,6880381⟩,
⟨64,231154430,231154562⟩]
theorem checked53342 : checkPrefixCuts (2^48) 6995574785 10 Manual.Count131072.C053342.packed 64 cuts53342 = true := by
 decide +kernel
def pointBounds53342 : List (Nat × Nat × Nat) := [(6995578880,112460925823126,112461313402214)]
theorem point_links_checked53342 : (cuts53342.take 1).map (fun c => (6995574785-1+2*2^10*c.k,112460918942749+c.lower,112461306521833+c.upper)) = pointBounds53342 := by
 decide +kernel
def cuts53343 : List PrefixCut := [⟨45,164199519,164199610⟩,
⟨64,232799748,232799878⟩]
theorem checked53343 : checkPrefixCuts (2^48) 6995705857 10 Manual.Count131072.C053343.packed 64 cuts53343 = true := by
 decide +kernel
def pointBounds53343 : List (Nat × Nat × Nat) := [(6995798016,112461314296698,112461701876005)]
theorem point_links_checked53343 : (cuts53343.take 1).map (fun c => (6995705857-1+2*2^10*c.k,112461150097179+c.lower,112461537676395+c.upper)) = pointBounds53343 := by
 decide +kernel
def cuts53344 : List PrefixCut := [⟨64,231628586,231628720⟩]
theorem checked53344 : checkPrefixCuts (2^48) 6995836929 10 Manual.Count131072.C053344.packed 64 cuts53344 = true := by
 decide +kernel
def cuts53345 : List PrefixCut := [⟨24,86381830,86381878⟩,
⟨64,230256309,230256438⟩]
theorem checked53345 : checkPrefixCuts (2^48) 6995968001 10 Manual.Count131072.C053345.packed 64 cuts53345 = true := by
 decide +kernel
def pointBounds53345 : List (Nat × Nat × Nat) := [(6996017152,112461700907343,112462088486871)]
theorem point_links_checked53345 : (cuts53345.take 1).map (fun c => (6995968001-1+2*2^10*c.k,112461614525513+c.lower,112462002104993+c.upper)) = pointBounds53345 := by
 decide +kernel
def cuts53346 : List PrefixCut := [⟨64,236488071,236488205⟩]
theorem checked53346 : checkPrefixCuts (2^48) 6996099073 10 Manual.Count131072.C053346.packed 64 cuts53346 = true := by
 decide +kernel
def cuts53347 : List PrefixCut := [⟨3,10943199,10943205⟩,
⟨64,234793901,234794035⟩]
theorem checked53347 : checkPrefixCuts (2^48) 6996230145 10 Manual.Count131072.C053347.packed 64 cuts53347 = true := by
 decide +kernel
def pointBounds53347 : List (Nat × Nat × Nat) := [(6996236288,112462092213092,112462479792841)]
theorem point_links_checked53347 : (cuts53347.take 1).map (fun c => (6996230145-1+2*2^10*c.k,112462081269893+c.lower,112462468849636+c.upper)) = pointBounds53347 := by
 decide +kernel
def cuts53348 : List PrefixCut := [⟨46,164626649,164626743⟩,
⟨64,229760579,229760711⟩]
theorem checked53348 : checkPrefixCuts (2^48) 6996361217 10 Manual.Count131072.C053348.packed 64 cuts53348 = true := by
 decide +kernel
def pointBounds53348 : List (Nat × Nat × Nat) := [(6996455424,112462480690443,112462868270414)]
theorem point_links_checked53348 : (cuts53348.take 1).map (fun c => (6996361217-1+2*2^10*c.k,112462316063794+c.lower,112462703643671+c.upper)) = pointBounds53348 := by
 decide +kernel
def cuts53349 : List PrefixCut := [⟨64,234583945,234584078⟩]
theorem checked53349 : checkPrefixCuts (2^48) 6996492289 10 Manual.Count131072.C053349.packed 64 cuts53349 = true := by
 decide +kernel
def cuts53350 : List PrefixCut := [⟨25,91080627,91080680⟩,
⟨64,232447372,232447504⟩]
theorem checked53350 : checkPrefixCuts (2^48) 6996623361 10 Manual.Count131072.C053350.packed 64 cuts53350 = true := by
 decide +kernel
def pointBounds53350 : List (Nat × Nat × Nat) := [(6996674560,112462871488945,112463259069140)]
theorem point_links_checked53350 : (cuts53350.take 1).map (fun c => (6996623361-1+2*2^10*c.k,112462780408318+c.lower,112463167988460+c.upper)) = pointBounds53350 := by
 decide +kernel
def cuts53351 : List PrefixCut := [⟨64,232885530,232885659⟩]
theorem checked53351 : checkPrefixCuts (2^48) 6996754433 10 Manual.Count131072.C053351.packed 64 cuts53351 = true := by
 decide +kernel
def cuts53352 : List PrefixCut := [⟨4,15085715,15085723⟩,
⟨64,232519099,232519231⟩]
theorem checked53352 : checkPrefixCuts (2^48) 6996885505 10 Manual.Count131072.C053352.packed 64 cuts53352 = true := by
 decide +kernel
def pointBounds53352 : List (Nat × Nat × Nat) := [(6996893696,112463260826935,112463648407346)]
theorem point_links_checked53352 : (cuts53352.take 1).map (fun c => (6996885505-1+2*2^10*c.k,112463245741220+c.lower,112463633321623+c.upper)) = pointBounds53352 := by
 decide +kernel
def cuts53353 : List PrefixCut := [⟨47,170524658,170524753⟩,
⟨64,232032034,232032165⟩]
theorem checked53353 : checkPrefixCuts (2^48) 6997016577 10 Manual.Count131072.C053353.packed 64 cuts53353 = true := by
 decide +kernel
def pointBounds53353 : List (Nat × Nat × Nat) := [(6997112832,112463648784977,112464036365607)]
theorem point_links_checked53353 : (cuts53353.take 1).map (fun c => (6997016577-1+2*2^10*c.k,112463478260319+c.lower,112463865840854+c.upper)) = pointBounds53353 := by
 decide +kernel
def cuts53354 : List PrefixCut := [⟨64,234803339,234803474⟩]
theorem checked53354 : checkPrefixCuts (2^48) 6997147649 10 Manual.Count131072.C053354.packed 64 cuts53354 = true := by
 decide +kernel
def cuts53355 : List PrefixCut := [⟨26,93204069,93204122⟩,
⟨64,234839127,234839259⟩]
theorem checked53355 : checkPrefixCuts (2^48) 6997278721 10 Manual.Count131072.C053355.packed 64 cuts53355 = true := by
 decide +kernel
def pointBounds53355 : List (Nat × Nat × Nat) := [(6997331968,112464038299761,112464425880615)]
theorem point_links_checked53355 : (cuts53355.take 1).map (fun c => (6997278721-1+2*2^10*c.k,112463945095692+c.lower,112464332676493+c.upper)) = pointBounds53355 := by
 decide +kernel
def cuts53356 : List PrefixCut := [⟨64,238977944,238978078⟩]
theorem checked53356 : checkPrefixCuts (2^48) 6997409793 10 Manual.Count131072.C053356.packed 64 cuts53356 = true := by
 decide +kernel
def cuts53357 : List PrefixCut := [⟨5,17739136,17739148⟩,
⟨64,234307447,234307582⟩]
theorem checked53357 : checkPrefixCuts (2^48) 6997540865 10 Manual.Count131072.C053357.packed 64 cuts53357 = true := by
 decide +kernel
def pointBounds53357 : List (Nat × Nat × Nat) := [(6997551104,112464436651899,112464824232978)]
theorem point_links_checked53357 : (cuts53357.take 1).map (fun c => (6997540865-1+2*2^10*c.k,112464418912763+c.lower,112464806493830+c.upper)) = pointBounds53357 := by
 decide +kernel
def cuts53358 : List PrefixCut := [⟨48,172600299,172600396⟩,
⟨64,229798001,229798131⟩]
theorem checked53358 : checkPrefixCuts (2^48) 6997671937 10 Manual.Count131072.C053358.packed 64 cuts53358 = true := by
 decide +kernel
def pointBounds53358 : List (Nat × Nat × Nat) := [(6997770240,112464825820509,112465213401808)]
theorem point_links_checked53358 : (cuts53358.take 1).map (fun c => (6997671937-1+2*2^10*c.k,112464653220210+c.lower,112465040801412+c.upper)) = pointBounds53358 := by
 decide +kernel
def cuts53359 : List PrefixCut := [⟨64,228989251,228989381⟩]
theorem checked53359 : checkPrefixCuts (2^48) 6997803009 10 Manual.Count131072.C053359.packed 64 cuts53359 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000104
