import PlattAssemblyKernel
import PlattCertificates.Count131072.C045344
import PlattCertificates.Count131072.C045345
import PlattCertificates.Count131072.C045346
import PlattCertificates.Count131072.C045347
import PlattCertificates.Count131072.C045348
import PlattCertificates.Count131072.C045349
import PlattCertificates.Count131072.C045350
import PlattCertificates.Count131072.C045351
import PlattCertificates.Count131072.C045352
import PlattCertificates.Count131072.C045353
import PlattCertificates.Count131072.C045354
import PlattCertificates.Count131072.C045355
import PlattCertificates.Count131072.C045356
import PlattCertificates.Count131072.C045357
import PlattCertificates.Count131072.C045358
import PlattCertificates.Count131072.C045359
import PlattCertificates.Count131072.C045360
import PlattCertificates.Count131072.C045361
import PlattCertificates.Count131072.C045362
import PlattCertificates.Count131072.C045363
import PlattCertificates.Count131072.C045364
import PlattCertificates.Count131072.C045365
import PlattCertificates.Count131072.C045366
import PlattCertificates.Count131072.C045367
import PlattCertificates.Count131072.C045368
import PlattCertificates.Count131072.C045369
import PlattCertificates.Count131072.C045370
import PlattCertificates.Count131072.C045371
import PlattCertificates.Count131072.C045372
import PlattCertificates.Count131072.C045373
import PlattCertificates.Count131072.C045374
import PlattCertificates.Count131072.C045375
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000167
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts45344 : List PrefixCut := [⟨64,272845752,272845907⟩]
theorem checked45344 : checkPrefixCuts (2^48) 5947260929 10 Manual.Count131072.C045344.packed 64 cuts45344 = true := by
 decide +kernel
def cuts45345 : List PrefixCut := [⟨26,110414445,110414510⟩,
⟨64,277335775,277335940⟩]
theorem checked45345 : checkPrefixCuts (2^48) 5947392001 10 Manual.Count131072.C045345.packed 64 cuts45345 = true := by
 decide +kernel
def pointBounds45345 : List (Nat × Nat × Nat) := [(5947445248,110438183613432,110438570037864)]
theorem point_links_checked45345 : (cuts45345.take 1).map (fun c => (5947392001-1+2*2^10*c.k,110438073198987+c.lower,110438459623354+c.upper)) = pointBounds45345 := by
 decide +kernel
def cuts45346 : List PrefixCut := [⟨53,229199685,229199816⟩,
⟨64,276430487,276430646⟩]
theorem checked45346 : checkPrefixCuts (2^48) 5947523073 10 Manual.Count131072.C045346.packed 64 cuts45346 = true := by
 decide +kernel
def pointBounds45346 : List (Nat × Nat × Nat) := [(5947631616,110438579734447,110438966159110)]
theorem point_links_checked45346 : (cuts45346.take 1).map (fun c => (5947523073-1+2*2^10*c.k,110438350534762+c.lower,110438736959294+c.upper)) = pointBounds45346 := by
 decide +kernel
def cuts45347 : List PrefixCut := [⟨64,277228914,277229067⟩]
theorem checked45347 : checkPrefixCuts (2^48) 5947654145 10 Manual.Count131072.C045347.packed 64 cuts45347 = true := by
 decide +kernel
def cuts45348 : List PrefixCut := [⟨16,66774438,66774477⟩,
⟨64,274099430,274099579⟩]
theorem checked45348 : checkPrefixCuts (2^48) 5947785217 10 Manual.Count131072.C045348.packed 64 cuts45348 = true := by
 decide +kernel
def pointBounds45348 : List (Nat × Nat × Nat) := [(5947817984,110438970968601,110439357393484)]
theorem point_links_checked45348 : (cuts45348.take 1).map (fun c => (5947785217-1+2*2^10*c.k,110438904194163+c.lower,110439290619007+c.upper)) = pointBounds45348 := by
 decide +kernel
def cuts45349 : List PrefixCut := [⟨43,183423668,183423774⟩,
⟨64,274424651,274424809⟩]
theorem checked45349 : checkPrefixCuts (2^48) 5947916289 10 Manual.Count131072.C045349.packed 64 cuts45349 = true := by
 decide +kernel
def pointBounds45349 : List (Nat × Nat × Nat) := [(5948004352,110439361717261,110439748142360)]
theorem point_links_checked45349 : (cuts45349.take 1).map (fun c => (5947916289-1+2*2^10*c.k,110439178293593+c.lower,110439564718586+c.upper)) = pointBounds45349 := by
 decide +kernel
def cuts45350 : List PrefixCut := [⟨64,272052518,272052677⟩]
theorem checked45350 : checkPrefixCuts (2^48) 5948047361 10 Manual.Count131072.C045350.packed 64 cuts45350 = true := by
 decide +kernel
def cuts45351 : List PrefixCut := [⟨6,25884665,25884681⟩,
⟨64,274838469,274838631⟩]
theorem checked45351 : checkPrefixCuts (2^48) 5948178433 10 Manual.Count131072.C045351.packed 64 cuts45351 = true := by
 decide +kernel
def pointBounds45351 : List (Nat × Nat × Nat) := [(5948190720,110439750655427,110440137080753)]
theorem point_links_checked45351 : (cuts45351.take 1).map (fun c => (5948178433-1+2*2^10*c.k,110439724770762+c.lower,110440111196072+c.upper)) = pointBounds45351 := by
 decide +kernel
def cuts45352 : List PrefixCut := [⟨33,142906049,142906129⟩,
⟨64,275210975,275211131⟩]
theorem checked45352 : checkPrefixCuts (2^48) 5948309505 10 Manual.Count131072.C045352.packed 64 cuts45352 = true := by
 decide +kernel
def pointBounds45352 : List (Nat × Nat × Nat) := [(5948377088,110440142515280,110440528940832)]
theorem point_links_checked45352 : (cuts45352.take 1).map (fun c => (5948309505-1+2*2^10*c.k,110439999609231+c.lower,110440386034703+c.upper)) = pointBounds45352 := by
 decide +kernel
def cuts45353 : List PrefixCut := [⟨60,259495320,259495469⟩,
⟨64,275867381,275867540⟩]
theorem checked45353 : checkPrefixCuts (2^48) 5948440577 10 Manual.Count131072.C045353.packed 64 cuts45353 = true := by
 decide +kernel
def pointBounds45353 : List (Nat × Nat × Nat) := [(5948563456,110440534315526,110440920741303)]
theorem point_links_checked45353 : (cuts45353.take 1).map (fun c => (5948440577-1+2*2^10*c.k,110440274820206+c.lower,110440661245834+c.upper)) = pointBounds45353 := by
 decide +kernel
def cuts45354 : List PrefixCut := [⟨64,274631062,274631217⟩]
theorem checked45354 : checkPrefixCuts (2^48) 5948571649 10 Manual.Count131072.C045354.packed 64 cuts45354 = true := by
 decide +kernel
def cuts45355 : List PrefixCut := [⟨23,100926803,100926862⟩,
⟨64,276517647,276517807⟩]
theorem checked45355 : checkPrefixCuts (2^48) 5948702721 10 Manual.Count131072.C045355.packed 64 cuts45355 = true := by
 decide +kernel
def pointBounds45355 : List (Nat × Nat × Nat) := [(5948749824,110440926245452,110441312671453)]
theorem point_links_checked45355 : (cuts45355.take 1).map (fun c => (5948702721-1+2*2^10*c.k,110440825318649+c.lower,110441211744591+c.upper)) = pointBounds45355 := by
 decide +kernel
def cuts45356 : List PrefixCut := [⟨50,211784499,211784617⟩,
⟨64,272678969,272679121⟩]
theorem checked45356 : checkPrefixCuts (2^48) 5948833793 10 Manual.Count131072.C045356.packed 64 cuts45356 = true := by
 decide +kernel
def pointBounds45356 : List (Nat × Nat × Nat) := [(5948936192,110441313620795,110441700047015)]
theorem point_links_checked45356 : (cuts45356.take 1).map (fun c => (5948833793-1+2*2^10*c.k,110441101836296+c.lower,110441488262398+c.upper)) = pointBounds45356 := by
 decide +kernel
def cuts45357 : List PrefixCut := [⟨64,277972184,277972341⟩]
theorem checked45357 : checkPrefixCuts (2^48) 5948964865 10 Manual.Count131072.C045357.packed 64 cuts45357 = true := by
 decide +kernel
def cuts45358 : List PrefixCut := [⟨13,54978622,54978652⟩,
⟨64,276593964,276594121⟩]
theorem checked45358 : checkPrefixCuts (2^48) 5949095937 10 Manual.Count131072.C045358.packed 64 cuts45358 = true := by
 decide +kernel
def pointBounds45358 : List (Nat × Nat × Nat) := [(5949122560,110441707466071,110442093892512)]
theorem point_links_checked45358 : (cuts45358.take 1).map (fun c => (5949095937-1+2*2^10*c.k,110441652487449+c.lower,110442038913860+c.upper)) = pointBounds45358 := by
 decide +kernel
def cuts45359 : List PrefixCut := [⟨40,172359531,172359630⟩,
⟨64,276304004,276304162⟩]
theorem checked45359 : checkPrefixCuts (2^48) 5949227009 10 Manual.Count131072.C045359.packed 64 cuts45359 = true := by
 decide +kernel
def pointBounds45359 : List (Nat × Nat × Nat) := [(5949308928,110442101440944,110442487867611)]
theorem point_links_checked45359 : (cuts45359.take 1).map (fun c => (5949227009-1+2*2^10*c.k,110441929081413+c.lower,110442315507981+c.upper)) = pointBounds45359 := by
 decide +kernel
def cuts45360 : List PrefixCut := [⟨64,276676405,276676567⟩]
theorem checked45360 : checkPrefixCuts (2^48) 5949358081 10 Manual.Count131072.C045360.packed 64 cuts45360 = true := by
 decide +kernel
def cuts45361 : List PrefixCut := [⟨3,13247008,13247016⟩,
⟨64,277994997,277995153⟩]
theorem checked45361 : checkPrefixCuts (2^48) 5949489153 10 Manual.Count131072.C045361.packed 64 cuts45361 = true := by
 decide +kernel
def pointBounds45361 : List (Nat × Nat × Nat) := [(5949495296,110442495308830,110442881735726)]
theorem point_links_checked45361 : (cuts45361.take 1).map (fun c => (5949489153-1+2*2^10*c.k,110442482061822+c.lower,110442868488710+c.upper)) = pointBounds45361 := by
 decide +kernel
def cuts45362 : List PrefixCut := [⟨30,128066775,128066843⟩,
⟨64,272595646,272595792⟩]
theorem checked45362 : checkPrefixCuts (2^48) 5949620225 10 Manual.Count131072.C045362.packed 64 cuts45362 = true := by
 decide +kernel
def pointBounds45362 : List (Nat × Nat × Nat) := [(5949681664,110442888123594,110443274550706)]
theorem point_links_checked45362 : (cuts45362.take 1).map (fun c => (5949620225-1+2*2^10*c.k,110442760056819+c.lower,110443146483863+c.upper)) = pointBounds45362 := by
 decide +kernel
def cuts45363 : List PrefixCut := [⟨57,246050042,246050190⟩,
⟨64,275664660,275664826⟩]
theorem checked45363 : checkPrefixCuts (2^48) 5949751297 10 Manual.Count131072.C045363.packed 64 cuts45363 = true := by
 decide +kernel
def pointBounds45363 : List (Nat × Nat × Nat) := [(5949868032,110443278702507,110443665129845)]
theorem point_links_checked45363 : (cuts45363.take 1).map (fun c => (5949751297-1+2*2^10*c.k,110443032652465+c.lower,110443419079655+c.upper)) = pointBounds45363 := by
 decide +kernel
def cuts45364 : List PrefixCut := [⟨64,276983173,276983335⟩]
theorem checked45364 : checkPrefixCuts (2^48) 5949882369 10 Manual.Count131072.C045364.packed 64 cuts45364 = true := by
 decide +kernel
def cuts45365 : List PrefixCut := [⟨20,84583908,84583955⟩,
⟨64,271300342,271300497⟩]
theorem checked45365 : checkPrefixCuts (2^48) 5950013441 10 Manual.Count131072.C045365.packed 64 cuts45365 = true := by
 decide +kernel
def pointBounds45365 : List (Nat × Nat × Nat) := [(5950054400,110443669884206,110444056311771)]
theorem point_links_checked45365 : (cuts45365.take 1).map (fun c => (5950013441-1+2*2^10*c.k,110443585300298+c.lower,110443971727816+c.upper)) = pointBounds45365 := by
 decide +kernel
def cuts45366 : List PrefixCut := [⟨47,200810456,200810574⟩,
⟨64,272997358,272997517⟩]
theorem checked45366 : checkPrefixCuts (2^48) 5950144513 10 Manual.Count131072.C045366.packed 64 cuts45366 = true := by
 decide +kernel
def pointBounds45366 : List (Nat × Nat × Nat) := [(5950240768,110444057411096,110444443838887)]
theorem point_links_checked45366 : (cuts45366.take 1).map (fun c => (5950144513-1+2*2^10*c.k,110443856600640+c.lower,110444243028313+c.upper)) = pointBounds45366 := by
 decide +kernel
def cuts45367 : List PrefixCut := [⟨64,274930818,274930977⟩]
theorem checked45367 : checkPrefixCuts (2^48) 5950275585 10 Manual.Count131072.C045367.packed 64 cuts45367 = true := by
 decide +kernel
def cuts45368 : List PrefixCut := [⟨10,43661027,43661053⟩,
⟨64,274735519,274735683⟩]
theorem checked45368 : checkPrefixCuts (2^48) 5950406657 10 Manual.Count131072.C045368.packed 64 cuts45368 = true := by
 decide +kernel
def pointBounds45368 : List (Nat × Nat × Nat) := [(5950427136,110444448189843,110444834617860)]
theorem point_links_checked45368 : (cuts45368.take 1).map (fun c => (5950406657-1+2*2^10*c.k,110444404528816+c.lower,110444790956807+c.upper)) = pointBounds45368 := by
 decide +kernel
def cuts45369 : List PrefixCut := [⟨37,160354207,160354300⟩,
⟨64,276952669,276952827⟩]
theorem checked45369 : checkPrefixCuts (2^48) 5950537729 10 Manual.Count131072.C045369.packed 64 cuts45369 = true := by
 decide +kernel
def pointBounds45369 : List (Nat × Nat × Nat) := [(5950613504,110444839618542,110445226046790)]
theorem point_links_checked45369 : (cuts45369.take 1).map (fun c => (5950537729-1+2*2^10*c.k,110444679264335+c.lower,110445065692490+c.upper)) = pointBounds45369 := by
 decide +kernel
def cuts45370 : List PrefixCut := [⟨64,274345013,274345172⟩]
theorem checked45370 : checkPrefixCuts (2^48) 5950668801 10 Manual.Count131072.C045370.packed 64 cuts45370 = true := by
 decide +kernel
def pointBounds45370 : List (Nat × Nat × Nat) := [(5950799872,110445230562017,110445616990489)]
theorem point_links_checked45370 : (cuts45370.take 1).map (fun c => (5950668801-1+2*2^10*c.k,110444956217004+c.lower,110445342645317+c.upper)) = pointBounds45370 := by
 decide +kernel
def cuts45371 : List PrefixCut := [⟨64,276136405,276136566⟩]
theorem checked45371 : checkPrefixCuts (2^48) 5950799873 10 Manual.Count131072.C045371.packed 64 cuts45371 = true := by
 decide +kernel
def cuts45372 : List PrefixCut := [⟨27,115835466,115835532⟩,
⟨64,273576189,273576345⟩]
theorem checked45372 : checkPrefixCuts (2^48) 5950930945 10 Manual.Count131072.C045372.packed 64 cuts45372 = true := by
 decide +kernel
def pointBounds45372 : List (Nat × Nat × Nat) := [(5950986240,110445622533888,110446008962587)]
theorem point_links_checked45372 : (cuts45372.take 1).map (fun c => (5950930945-1+2*2^10*c.k,110445506698422+c.lower,110445893127055+c.upper)) = pointBounds45372 := by
 decide +kernel
def cuts45373 : List PrefixCut := [⟨54,228732288,228732421⟩,
⟨64,272624184,272624340⟩]
theorem checked45373 : checkPrefixCuts (2^48) 5951062017 10 Manual.Count131072.C045373.packed 64 cuts45373 = true := by
 decide +kernel
def pointBounds45373 : List (Nat × Nat × Nat) := [(5951172608,110446009006899,110446395435821)]
theorem point_links_checked45373 : (cuts45373.take 1).map (fun c => (5951062017-1+2*2^10*c.k,110445780274611+c.lower,110446166703400+c.upper)) = pointBounds45373 := by
 decide +kernel
def cuts45374 : List PrefixCut := [⟨64,272854680,272854837⟩]
theorem checked45374 : checkPrefixCuts (2^48) 5951193089 10 Manual.Count131072.C045374.packed 64 cuts45374 = true := by
 decide +kernel
def cuts45375 : List PrefixCut := [⟨17,72457536,72457577⟩,
⟨64,274314837,274314991⟩]
theorem checked45375 : checkPrefixCuts (2^48) 5951324161 10 Manual.Count131072.C045375.packed 64 cuts45375 = true := by
 decide +kernel
def pointBounds45375 : List (Nat × Nat × Nat) := [(5951358976,110446398211011,110446784640154)]
theorem point_links_checked45375 : (cuts45375.take 1).map (fun c => (5951324161-1+2*2^10*c.k,110446325753475+c.lower,110446712182577+c.upper)) = pointBounds45375 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000167
