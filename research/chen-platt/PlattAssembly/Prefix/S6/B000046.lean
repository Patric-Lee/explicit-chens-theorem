import PlattAssemblyKernel
import PlattCertificates.Count131072.C051472
import PlattCertificates.Count131072.C051473
import PlattCertificates.Count131072.C051474
import PlattCertificates.Count131072.C051475
import PlattCertificates.Count131072.C051476
import PlattCertificates.Count131072.C051477
import PlattCertificates.Count131072.C051478
import PlattCertificates.Count131072.C051479
import PlattCertificates.Count131072.C051480
import PlattCertificates.Count131072.C051481
import PlattCertificates.Count131072.C051482
import PlattCertificates.Count131072.C051483
import PlattCertificates.Count131072.C051484
import PlattCertificates.Count131072.C051485
import PlattCertificates.Count131072.C051486
import PlattCertificates.Count131072.C051487
import PlattCertificates.Count131072.C051488
import PlattCertificates.Count131072.C051489
import PlattCertificates.Count131072.C051490
import PlattCertificates.Count131072.C051491
import PlattCertificates.Count131072.C051492
import PlattCertificates.Count131072.C051493
import PlattCertificates.Count131072.C051494
import PlattCertificates.Count131072.C051495
import PlattCertificates.Count131072.C051496
import PlattCertificates.Count131072.C051497
import PlattCertificates.Count131072.C051498
import PlattCertificates.Count131072.C051499
import PlattCertificates.Count131072.C051500
import PlattCertificates.Count131072.C051501
import PlattCertificates.Count131072.C051502
import PlattCertificates.Count131072.C051503
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000046
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts51472 : List PrefixCut := [⟨64,240840003,240840135⟩]
theorem checked51472 : checkPrefixCuts (2^48) 6750470145 10 Manual.Count131072.C051472.packed 64 cuts51472 = true := by
 decide +kernel
def cuts51473 : List PrefixCut := [⟨3,11174595,11174601⟩,
⟨64,242794995,242795138⟩]
theorem checked51473 : checkPrefixCuts (2^48) 6750601217 10 Manual.Count131072.C051473.packed 64 cuts51473 = true := by
 decide +kernel
def pointBounds51473 : List (Nat × Nat × Nat) := [(6750607360,112017977104040,112018364431438)]
theorem point_links_checked51473 : (cuts51473.take 1).map (fun c => (6750601217-1+2*2^10*c.k,112017965929445+c.lower,112018353256837+c.upper)) = pointBounds51473 := by
 decide +kernel
def cuts51474 : List PrefixCut := [⟨43,164987862,164987955⟩,
⟨64,245500490,245500630⟩]
theorem checked51474 : checkPrefixCuts (2^48) 6750732289 10 Manual.Count131072.C051474.packed 64 cuts51474 = true := by
 decide +kernel
def pointBounds51474 : List (Nat × Nat × Nat) := [(6750820352,112018373712302,112018761039930)]
theorem point_links_checked51474 : (cuts51474.take 1).map (fun c => (6750732289-1+2*2^10*c.k,112018208724440+c.lower,112018596051975+c.upper)) = pointBounds51474 := by
 decide +kernel
def cuts51475 : List PrefixCut := [⟨64,241034420,241034561⟩]
theorem checked51475 : checkPrefixCuts (2^48) 6750863361 10 Manual.Count131072.C051475.packed 64 cuts51475 = true := by
 decide +kernel
def cuts51476 : List PrefixCut := [⟨19,71004410,71004452⟩,
⟨64,239612184,239612324⟩]
theorem checked51476 : checkPrefixCuts (2^48) 6750994433 10 Manual.Count131072.C051476.packed 64 cuts51476 = true := by
 decide +kernel
def pointBounds51476 : List (Nat × Nat × Nat) := [(6751033344,112018766263760,112019153591618)]
theorem point_links_checked51476 : (cuts51476.take 1).map (fun c => (6750994433-1+2*2^10*c.k,112018695259350+c.lower,112019082587166+c.upper)) = pointBounds51476 := by
 decide +kernel
def cuts51477 : List PrefixCut := [⟨59,224098046,224098174⟩,
⟨64,242192484,242192623⟩]
theorem checked51477 : checkPrefixCuts (2^48) 6751125505 10 Manual.Count131072.C051477.packed 64 cuts51477 = true := by
 decide +kernel
def pointBounds51477 : List (Nat × Nat × Nat) := [(6751246336,112019158969580,112019546297664)]
theorem point_links_checked51477 : (cuts51477.take 1).map (fun c => (6751125505-1+2*2^10*c.k,112018934871534+c.lower,112019322199490+c.upper)) = pointBounds51477 := by
 decide +kernel
def cuts51478 : List PrefixCut := [⟨64,241020402,241020535⟩]
theorem checked51478 : checkPrefixCuts (2^48) 6751256577 10 Manual.Count131072.C051478.packed 64 cuts51478 = true := by
 decide +kernel
def cuts51479 : List PrefixCut := [⟨35,130660198,130660269⟩,
⟨64,240098514,240098647⟩]
theorem checked51479 : checkPrefixCuts (2^48) 6751387649 10 Manual.Count131072.C051479.packed 64 cuts51479 = true := by
 decide +kernel
def pointBounds51479 : List (Nat × Nat × Nat) := [(6751459328,112019548744618,112019936072917)]
theorem point_links_checked51479 : (cuts51479.take 1).map (fun c => (6751387649-1+2*2^10*c.k,112019418084420+c.lower,112019805412648+c.upper)) = pointBounds51479 := by
 decide +kernel
def cuts51480 : List PrefixCut := [⟨64,241636385,241636522⟩]
theorem checked51480 : checkPrefixCuts (2^48) 6751518721 10 Manual.Count131072.C051480.packed 64 cuts51480 = true := by
 decide +kernel
def cuts51481 : List PrefixCut := [⟨11,41231140,41231163⟩,
⟨64,245425441,245425583⟩]
theorem checked51481 : checkPrefixCuts (2^48) 6751649793 10 Manual.Count131072.C051481.packed 64 cuts51481 = true := by
 decide +kernel
def pointBounds51481 : List (Nat × Nat × Nat) := [(6751672320,112019941050459,112020328378980)]
theorem point_links_checked51481 : (cuts51481.take 1).map (fun c => (6751649793-1+2*2^10*c.k,112019899819319+c.lower,112020287147817+c.upper)) = pointBounds51481 := by
 decide +kernel
def cuts51482 : List PrefixCut := [⟨51,194144096,194144205⟩,
⟨64,242460787,242460924⟩]
theorem checked51482 : checkPrefixCuts (2^48) 6751780865 10 Manual.Count131072.C051482.packed 64 cuts51482 = true := by
 decide +kernel
def pointBounds51482 : List (Nat × Nat × Nat) := [(6751885312,112020339388856,112020726717605)]
theorem point_links_checked51482 : (cuts51482.take 1).map (fun c => (6751780865-1+2*2^10*c.k,112020145244760+c.lower,112020532573400+c.upper)) = pointBounds51482 := by
 decide +kernel
def cuts51483 : List PrefixCut := [⟨64,243956853,243956984⟩]
theorem checked51483 : checkPrefixCuts (2^48) 6751911937 10 Manual.Count131072.C051483.packed 64 cuts51483 = true := by
 decide +kernel
def cuts51484 : List PrefixCut := [⟨27,99882528,99882583⟩,
⟨64,241159061,241159197⟩]
theorem checked51484 : checkPrefixCuts (2^48) 6752043009 10 Manual.Count131072.C051484.packed 64 cuts51484 = true := by
 decide +kernel
def pointBounds51484 : List (Nat × Nat × Nat) := [(6752098304,112020731544928,112021118873891)]
theorem point_links_checked51484 : (cuts51484.take 1).map (fun c => (6752043009-1+2*2^10*c.k,112020631662400+c.lower,112021018991308+c.upper)) = pointBounds51484 := by
 decide +kernel
def cuts51485 : List PrefixCut := [⟨64,241654620,241654757⟩]
theorem checked51485 : checkPrefixCuts (2^48) 6752174081 10 Manual.Count131072.C051485.packed 64 cuts51485 = true := by
 decide +kernel
def cuts51486 : List PrefixCut := [⟨3,11505261,11505268⟩,
⟨64,241191404,241191542⟩]
theorem checked51486 : checkPrefixCuts (2^48) 6752305153 10 Manual.Count131072.C051486.packed 64 cuts51486 = true := by
 decide +kernel
def pointBounds51486 : List (Nat × Nat × Nat) := [(6752311296,112021125981342,112021513310530)]
theorem point_links_checked51486 : (cuts51486.take 1).map (fun c => (6752305153-1+2*2^10*c.k,112021114476081+c.lower,112021501805262+c.upper)) = pointBounds51486 := by
 decide +kernel
def cuts51487 : List PrefixCut := [⟨43,162278400,162278492⟩,
⟨64,240978288,240978425⟩]
theorem checked51487 : checkPrefixCuts (2^48) 6752436225 10 Manual.Count131072.C051487.packed 64 cuts51487 = true := by
 decide +kernel
def pointBounds51487 : List (Nat × Nat × Nat) := [(6752524288,112021517945885,112021905275296)]
theorem point_links_checked51487 : (cuts51487.take 1).map (fun c => (6752436225-1+2*2^10*c.k,112021355667485+c.lower,112021742996804+c.upper)) = pointBounds51487 := by
 decide +kernel
def cuts51488 : List PrefixCut := [⟨64,245392087,245392227⟩]
theorem checked51488 : checkPrefixCuts (2^48) 6752567297 10 Manual.Count131072.C051488.packed 64 cuts51488 = true := by
 decide +kernel
def cuts51489 : List PrefixCut := [⟨19,72028575,72028616⟩,
⟨64,241802597,241802738⟩]
theorem checked51489 : checkPrefixCuts (2^48) 6752698369 10 Manual.Count131072.C051489.packed 64 cuts51489 = true := by
 decide +kernel
def pointBounds51489 : List (Nat × Nat × Nat) := [(6752737280,112021914066435,112022301396072)]
theorem point_links_checked51489 : (cuts51489.take 1).map (fun c => (6752698369-1+2*2^10*c.k,112021842037860+c.lower,112022229367456+c.upper)) = pointBounds51489 := by
 decide +kernel
def cuts51490 : List PrefixCut := [⟨59,221415511,221415637⟩,
⟨64,239713793,239713929⟩]
theorem checked51490 : checkPrefixCuts (2^48) 6752829441 10 Manual.Count131072.C051490.packed 64 cuts51490 = true := by
 decide +kernel
def pointBounds51490 : List (Nat × Nat × Nat) := [(6752950272,112022305255968,112022692585831)]
theorem point_links_checked51490 : (cuts51490.take 1).map (fun c => (6752829441-1+2*2^10*c.k,112022083840457+c.lower,112022471170194+c.upper)) = pointBounds51490 := by
 decide +kernel
def cuts51491 : List PrefixCut := [⟨64,242501778,242501914⟩]
theorem checked51491 : checkPrefixCuts (2^48) 6752960513 10 Manual.Count131072.C051491.packed 64 cuts51491 = true := by
 decide +kernel
def cuts51492 : List PrefixCut := [⟨35,129585221,129585297⟩,
⟨64,239454404,239454546⟩]
theorem checked51492 : checkPrefixCuts (2^48) 6753091585 10 Manual.Count131072.C051492.packed 64 cuts51492 = true := by
 decide +kernel
def pointBounds51492 : List (Nat × Nat × Nat) := [(6753163264,112022695641249,112023082971334)]
theorem point_links_checked51492 : (cuts51492.take 1).map (fun c => (6753091585-1+2*2^10*c.k,112022566056028+c.lower,112022953386037+c.upper)) = pointBounds51492 := by
 decide +kernel
def cuts51493 : List PrefixCut := [⟨64,243325979,243326117⟩]
theorem checked51493 : checkPrefixCuts (2^48) 6753222657 10 Manual.Count131072.C051493.packed 64 cuts51493 = true := by
 decide +kernel
def cuts51494 : List PrefixCut := [⟨11,42929583,42929607⟩,
⟨64,241737467,241737607⟩]
theorem checked51494 : checkPrefixCuts (2^48) 6753353729 10 Manual.Count131072.C051494.packed 64 cuts51494 = true := by
 decide +kernel
def pointBounds51494 : List (Nat × Nat × Nat) := [(6753376256,112023091765994,112023479096307)]
theorem point_links_checked51494 : (cuts51494.take 1).map (fun c => (6753353729-1+2*2^10*c.k,112023048836411+c.lower,112023436166700+c.upper)) = pointBounds51494 := by
 decide +kernel
def cuts51495 : List PrefixCut := [⟨51,191969525,191969638⟩,
⟨64,239065373,239065513⟩]
theorem checked51495 : checkPrefixCuts (2^48) 6753484801 10 Manual.Count131072.C051495.packed 64 cuts51495 = true := by
 decide +kernel
def pointBounds51495 : List (Nat × Nat × Nat) := [(6753589248,112023482543403,112023869873945)]
theorem point_links_checked51495 : (cuts51495.take 1).map (fun c => (6753484801-1+2*2^10*c.k,112023290573878+c.lower,112023677904307+c.upper)) = pointBounds51495 := by
 decide +kernel
def cuts51496 : List PrefixCut := [⟨64,239519178,239519315⟩]
theorem checked51496 : checkPrefixCuts (2^48) 6753615873 10 Manual.Count131072.C051496.packed 64 cuts51496 = true := by
 decide +kernel
def cuts51497 : List PrefixCut := [⟨27,100107382,100107439⟩,
⟨64,239264461,239264597⟩]
theorem checked51497 : checkPrefixCuts (2^48) 6753746945 10 Manual.Count131072.C051497.packed 64 cuts51497 = true := by
 decide +kernel
def pointBounds51497 : List (Nat × Nat × Nat) := [(6753802240,112023869265811,112024256596574)]
theorem point_links_checked51497 : (cuts51497.take 1).map (fun c => (6753746945-1+2*2^10*c.k,112023769158429+c.lower,112024156489135+c.upper)) = pointBounds51497 := by
 decide +kernel
def cuts51498 : List PrefixCut := [⟨64,240843486,240843624⟩]
theorem checked51498 : checkPrefixCuts (2^48) 6753878017 10 Manual.Count131072.C051498.packed 64 cuts51498 = true := by
 decide +kernel
def cuts51499 : List PrefixCut := [⟨3,11460683,11460689⟩,
⟨64,239005133,239005268⟩]
theorem checked51499 : checkPrefixCuts (2^48) 6754009089 10 Manual.Count131072.C051499.packed 64 cuts51499 = true := by
 decide +kernel
def pointBounds51499 : List (Nat × Nat × Nat) := [(6754015232,112024260727059,112024648058045)]
theorem point_links_checked51499 : (cuts51499.take 1).map (fun c => (6754009089-1+2*2^10*c.k,112024249266376+c.lower,112024636597356+c.upper)) = pointBounds51499 := by
 decide +kernel
def cuts51500 : List PrefixCut := [⟨43,161820729,161820821⟩,
⟨64,242542780,242542918⟩]
theorem checked51500 : checkPrefixCuts (2^48) 6754140161 10 Manual.Count131072.C051500.packed 64 cuts51500 = true := by
 decide +kernel
def pointBounds51500 : List (Nat × Nat × Nat) := [(6754228224,112024650092238,112025037423445)]
theorem point_links_checked51500 : (cuts51500.take 1).map (fun c => (6754140161-1+2*2^10*c.k,112024488271509+c.lower,112024875602624+c.upper)) = pointBounds51500 := by
 decide +kernel
def cuts51501 : List PrefixCut := [⟨64,240871155,240871294⟩]
theorem checked51501 : checkPrefixCuts (2^48) 6754271233 10 Manual.Count131072.C051501.packed 64 cuts51501 = true := by
 decide +kernel
def cuts51502 : List PrefixCut := [⟨19,72927197,72927238⟩,
⟨64,244366963,244367097⟩]
theorem checked51502 : checkPrefixCuts (2^48) 6754402305 10 Manual.Count131072.C051502.packed 64 cuts51502 = true := by
 decide +kernel
def pointBounds51502 : List (Nat × Nat × Nat) := [(6754441216,112025044612641,112025431944074)]
theorem point_links_checked51502 : (cuts51502.take 1).map (fun c => (6754402305-1+2*2^10*c.k,112024971685444+c.lower,112025359016836+c.upper)) = pointBounds51502 := by
 decide +kernel
def cuts51503 : List PrefixCut := [⟨59,220026177,220026304⟩,
⟨64,239653321,239653459⟩]
theorem checked51503 : checkPrefixCuts (2^48) 6754533377 10 Manual.Count131072.C051503.packed 64 cuts51503 = true := by
 decide +kernel
def pointBounds51503 : List (Nat × Nat × Nat) := [(6754654208,112025436078584,112025823410237)]
theorem point_links_checked51503 : (cuts51503.take 1).map (fun c => (6754533377-1+2*2^10*c.k,112025216052407+c.lower,112025603383933+c.upper)) = pointBounds51503 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000046
