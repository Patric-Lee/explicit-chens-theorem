import PlattAssemblyKernel
import PlattCertificates.Count131072.C034512
import PlattCertificates.Count131072.C034513
import PlattCertificates.Count131072.C034514
import PlattCertificates.Count131072.C034515
import PlattCertificates.Count131072.C034516
import PlattCertificates.Count131072.C034517
import PlattCertificates.Count131072.C034518
import PlattCertificates.Count131072.C034519
import PlattCertificates.Count131072.C034520
import PlattCertificates.Count131072.C034521
import PlattCertificates.Count131072.C034522
import PlattCertificates.Count131072.C034523
import PlattCertificates.Count131072.C034524
import PlattCertificates.Count131072.C034525
import PlattCertificates.Count131072.C034526
import PlattCertificates.Count131072.C034527
import PlattCertificates.Count131072.C034528
import PlattCertificates.Count131072.C034529
import PlattCertificates.Count131072.C034530
import PlattCertificates.Count131072.C034531
import PlattCertificates.Count131072.C034532
import PlattCertificates.Count131072.C034533
import PlattCertificates.Count131072.C034534
import PlattCertificates.Count131072.C034535
import PlattCertificates.Count131072.C034536
import PlattCertificates.Count131072.C034537
import PlattCertificates.Count131072.C034538
import PlattCertificates.Count131072.C034539
import PlattCertificates.Count131072.C034540
import PlattCertificates.Count131072.C034541
import PlattCertificates.Count131072.C034542
import PlattCertificates.Count131072.C034543
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000141
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts34512 : List PrefixCut := [⟨33,185700992,185701108⟩,
⟨64,365244584,365244816⟩]
theorem checked34512 : checkPrefixCuts (2^48) 4527489025 10 Manual.Count131072.C034512.packed 64 cuts34512 = true := by
 decide +kernel
def pointBounds34512 : List (Nat × Nat × Nat) := [(4527556608,107005832463283,107006216834941)]
theorem point_links_checked34512 : (cuts34512.take 1).map (fun c => (4527489025-1+2*2^10*c.k,107005646762291+c.lower,107006031133833+c.upper)) = pointBounds34512 := by
 decide +kernel
def cuts34513 : List PrefixCut := [⟨39,219203818,219203960⟩,
⟨64,362560812,362561048⟩]
theorem checked34513 : checkPrefixCuts (2^48) 4527620097 10 Manual.Count131072.C034513.packed 64 cuts34513 = true := by
 decide +kernel
def pointBounds34513 : List (Nat × Nat × Nat) := [(4527699968,107006231210693,107006615582609)]
theorem point_links_checked34513 : (cuts34513.take 1).map (fun c => (4527620097-1+2*2^10*c.k,107006012006875+c.lower,107006396378649+c.upper)) = pointBounds34513 := by
 decide +kernel
def cuts34514 : List PrefixCut := [⟨45,254818293,254818452⟩,
⟨64,362799014,362799240⟩]
theorem checked34514 : checkPrefixCuts (2^48) 4527751169 10 Manual.Count131072.C034514.packed 64 cuts34514 = true := by
 decide +kernel
def pointBounds34514 : List (Nat × Nat × Nat) := [(4527843328,107006629385980,107007013758149)]
theorem point_links_checked34514 : (cuts34514.take 1).map (fun c => (4527751169-1+2*2^10*c.k,107006374567687+c.lower,107006758939697+c.upper)) = pointBounds34514 := by
 decide +kernel
def cuts34515 : List PrefixCut := [⟨51,293352301,293352480⟩,
⟨64,364839955,364840183⟩]
theorem checked34515 : checkPrefixCuts (2^48) 4527882241 10 Manual.Count131072.C034515.packed 64 cuts34515 = true := by
 decide +kernel
def pointBounds34515 : List (Nat × Nat × Nat) := [(4527986688,107007030719002,107007415091417)]
theorem point_links_checked34515 : (cuts34515.take 1).map (fun c => (4527882241-1+2*2^10*c.k,107006737366701+c.lower,107007121738937+c.upper)) = pointBounds34515 := by
 decide +kernel
def cuts34516 : List PrefixCut := [⟨57,331075888,331076093⟩,
⟨64,371356410,371356640⟩]
theorem checked34516 : checkPrefixCuts (2^48) 4528013313 10 Manual.Count131072.C034516.packed 64 cuts34516 = true := by
 decide +kernel
def pointBounds34516 : List (Nat × Nat × Nat) := [(4528130048,107007433282544,107007817655213)]
theorem point_links_checked34516 : (cuts34516.take 1).map (fun c => (4528013313-1+2*2^10*c.k,107007102206656+c.lower,107007486579120+c.upper)) = pointBounds34516 := by
 decide +kernel
def cuts34517 : List PrefixCut := [⟨63,365378293,365378517⟩,
⟨64,371159119,371159346⟩]
theorem checked34517 : checkPrefixCuts (2^48) 4528144385 10 Manual.Count131072.C034517.packed 64 cuts34517 = true := by
 decide +kernel
def pointBounds34517 : List (Nat × Nat × Nat) := [(4528273408,107007838941359,107008223314277)]
theorem point_links_checked34517 : (cuts34517.take 1).map (fun c => (4528144385-1+2*2^10*c.k,107007473563066+c.lower,107007857935760+c.upper)) = pointBounds34517 := by
 decide +kernel
def cuts34518 : List PrefixCut := [⟨64,369097132,369097367⟩]
theorem checked34518 : checkPrefixCuts (2^48) 4528275457 10 Manual.Count131072.C034518.packed 64 cuts34518 = true := by
 decide +kernel
def cuts34519 : List PrefixCut := [⟨5,28405992,28406010⟩,
⟨64,366351587,366351815⟩]
theorem checked34519 : checkPrefixCuts (2^48) 4528406529 10 Manual.Count131072.C034519.packed 64 cuts34519 = true := by
 decide +kernel
def pointBounds34519 : List (Nat × Nat × Nat) := [(4528416768,107008242225309,107008626598483)]
theorem point_links_checked34519 : (cuts34519.take 1).map (fun c => (4528406529-1+2*2^10*c.k,107008213819317+c.lower,107008598192473+c.upper)) = pointBounds34519 := by
 decide +kernel
def cuts34520 : List PrefixCut := [⟨11,62466426,62466464⟩,
⟨64,365284355,365284585⟩]
theorem checked34520 : checkPrefixCuts (2^48) 4528537601 10 Manual.Count131072.C034520.packed 64 cuts34520 = true := by
 decide +kernel
def pointBounds34520 : List (Nat × Nat × Nat) := [(4528560128,107008642637330,107009027010752)]
theorem point_links_checked34520 : (cuts34520.take 1).map (fun c => (4528537601-1+2*2^10*c.k,107008580170904+c.lower,107008964544288+c.upper)) = pointBounds34520 := by
 decide +kernel
def cuts34521 : List PrefixCut := [⟨17,97457104,97457168⟩,
⟨64,369624485,369624715⟩]
theorem checked34521 : checkPrefixCuts (2^48) 4528668673 10 Manual.Count131072.C034521.packed 64 cuts34521 = true := by
 decide +kernel
def pointBounds34521 : List (Nat × Nat × Nat) := [(4528703488,107009042912363,107009427286041)]
theorem point_links_checked34521 : (cuts34521.take 1).map (fun c => (4528668673-1+2*2^10*c.k,107008945455259+c.lower,107009329828873+c.upper)) = pointBounds34521 := by
 decide +kernel
def cuts34522 : List PrefixCut := [⟨23,129710971,129711050⟩,
⟨64,364206609,364206839⟩]
theorem checked34522 : checkPrefixCuts (2^48) 4528799745 10 Manual.Count131072.C034522.packed 64 cuts34522 = true := by
 decide +kernel
def pointBounds34522 : List (Nat × Nat × Nat) := [(4528846848,107009444790715,107009829164638)]
theorem point_links_checked34522 : (cuts34522.take 1).map (fun c => (4528799745-1+2*2^10*c.k,107009315079744+c.lower,107009699453588+c.upper)) = pointBounds34522 := by
 decide +kernel
def cuts34523 : List PrefixCut := [⟨29,165629733,165629836⟩,
⟨64,365874134,365874363⟩]
theorem checked34523 : checkPrefixCuts (2^48) 4528930817 10 Manual.Count131072.C034523.packed 64 cuts34523 = true := by
 decide +kernel
def pointBounds34523 : List (Nat × Nat × Nat) := [(4528990208,107009844916086,107010229290263)]
theorem point_links_checked34523 : (cuts34523.take 1).map (fun c => (4528930817-1+2*2^10*c.k,107009679286353+c.lower,107010063660427+c.upper)) = pointBounds34523 := by
 decide +kernel
def cuts34524 : List PrefixCut := [⟨35,204094429,204094557⟩,
⟨64,372575519,372575753⟩]
theorem checked34524 : checkPrefixCuts (2^48) 4529061889 10 Manual.Count131072.C034524.packed 64 cuts34524 = true := by
 decide +kernel
def pointBounds34524 : List (Nat × Nat × Nat) := [(4529133568,107010249254916,107010633629347)]
theorem point_links_checked34524 : (cuts34524.take 1).map (fun c => (4529061889-1+2*2^10*c.k,107010045160487+c.lower,107010429534790+c.upper)) = pointBounds34524 := by
 decide +kernel
def cuts34525 : List PrefixCut := [⟨41,234291289,234291440⟩,
⟨64,367717318,367717551⟩]
theorem checked34525 : checkPrefixCuts (2^48) 4529192961 10 Manual.Count131072.C034525.packed 64 cuts34525 = true := by
 decide +kernel
def pointBounds34525 : List (Nat × Nat × Nat) := [(4529276928,107010652027295,107011036401983)]
theorem point_links_checked34525 : (cuts34525.take 1).map (fun c => (4529192961-1+2*2^10*c.k,107010417736006+c.lower,107010802110543+c.upper)) = pointBounds34525 := by
 decide +kernel
def cuts34526 : List PrefixCut := [⟨47,269147177,269147348⟩,
⟨64,365096663,365096894⟩]
theorem checked34526 : checkPrefixCuts (2^48) 4529324033 10 Manual.Count131072.C034526.packed 64 cuts34526 = true := by
 decide +kernel
def pointBounds34526 : List (Nat × Nat × Nat) := [(4529420288,107011054600501,107011438975442)]
theorem point_links_checked34526 : (cuts34526.take 1).map (fun c => (4529324033-1+2*2^10*c.k,107010785453324+c.lower,107011169828094+c.upper)) = pointBounds34526 := by
 decide +kernel
def cuts34527 : List PrefixCut := [⟨53,304746676,304746868⟩,
⟨64,369498182,369498415⟩]
theorem checked34527 : checkPrefixCuts (2^48) 4529455105 10 Manual.Count131072.C034527.packed 64 cuts34527 = true := by
 decide +kernel
def pointBounds34527 : List (Nat × Nat × Nat) := [(4529563648,107011455296663,107011839671856)]
theorem point_links_checked34527 : (cuts34527.take 1).map (fun c => (4529455105-1+2*2^10*c.k,107011150549987+c.lower,107011534924988+c.upper)) = pointBounds34527 := by
 decide +kernel
def cuts34528 : List PrefixCut := [⟨59,339598309,339598523⟩,
⟨64,367623307,367623540⟩]
theorem checked34528 : checkPrefixCuts (2^48) 4529586177 10 Manual.Count131072.C034528.packed 64 cuts34528 = true := by
 decide +kernel
def pointBounds34528 : List (Nat × Nat × Nat) := [(4529707008,107011859646478,107012244021926)]
theorem point_links_checked34528 : (cuts34528.take 1).map (fun c => (4529586177-1+2*2^10*c.k,107011520048169+c.lower,107011904423403+c.upper)) = pointBounds34528 := by
 decide +kernel
def cuts34529 : List PrefixCut := [⟨64,363325109,363325334⟩]
theorem checked34529 : checkPrefixCuts (2^48) 4529717249 10 Manual.Count131072.C034529.packed 64 cuts34529 = true := by
 decide +kernel
def cuts34530 : List PrefixCut := [⟨1,5095300,5095303⟩,
⟨64,366483511,366483741⟩]
theorem checked34530 : checkPrefixCuts (2^48) 4529848321 10 Manual.Count131072.C034530.packed 64 cuts34530 = true := by
 decide +kernel
def pointBounds34530 : List (Nat × Nat × Nat) := [(4529850368,107012256091885,107012640467580)]
theorem point_links_checked34530 : (cuts34530.take 1).map (fun c => (4529848321-1+2*2^10*c.k,107012250996585+c.lower,107012635372277+c.upper)) = pointBounds34530 := by
 decide +kernel
def cuts34531 : List PrefixCut := [⟨7,38648543,38648567⟩,
⟨64,366100134,366100351⟩]
theorem checked34531 : checkPrefixCuts (2^48) 4529979393 10 Manual.Count131072.C034531.packed 64 cuts34531 = true := by
 decide +kernel
def pointBounds34531 : List (Nat × Nat × Nat) := [(4529993728,107012656128639,107013040504585)]
theorem point_links_checked34531 : (cuts34531.take 1).map (fun c => (4529979393-1+2*2^10*c.k,107012617480096+c.lower,107013001856018+c.upper)) = pointBounds34531 := by
 decide +kernel
def cuts34532 : List PrefixCut := [⟨13,74498715,74498762⟩,
⟨64,363355678,363355905⟩]
theorem checked34532 : checkPrefixCuts (2^48) 4530110465 10 Manual.Count131072.C034532.packed 64 cuts34532 = true := by
 decide +kernel
def pointBounds34532 : List (Nat × Nat × Nat) := [(4530137088,107013058078945,107013442455131)]
theorem point_links_checked34532 : (cuts34532.take 1).map (fun c => (4530110465-1+2*2^10*c.k,107012983580230+c.lower,107013367956369+c.upper)) = pointBounds34532 := by
 decide +kernel
def cuts34533 : List PrefixCut := [⟨19,107737164,107737229⟩,
⟨64,364028628,364028853⟩]
theorem checked34533 : checkPrefixCuts (2^48) 4530241537 10 Manual.Count131072.C034533.packed 64 cuts34533 = true := by
 decide +kernel
def pointBounds34533 : List (Nat × Nat × Nat) := [(4530280448,107013454673072,107013839049503)]
theorem point_links_checked34533 : (cuts34533.take 1).map (fun c => (4530241537-1+2*2^10*c.k,107013346935908+c.lower,107013731312274+c.upper)) = pointBounds34533 := by
 decide +kernel
def cuts34534 : List PrefixCut := [⟨25,141097850,141097937⟩,
⟨64,366689624,366689848⟩]
theorem checked34534 : checkPrefixCuts (2^48) 4530372609 10 Manual.Count131072.C034534.packed 64 cuts34534 = true := by
 decide +kernel
def pointBounds34534 : List (Nat × Nat × Nat) := [(4530423808,107013852062386,107014236439064)]
theorem point_links_checked34534 : (cuts34534.take 1).map (fun c => (4530372609-1+2*2^10*c.k,107013710964536+c.lower,107014095341127+c.upper)) = pointBounds34534 := by
 decide +kernel
def cuts34535 : List PrefixCut := [⟨31,179799560,179799671⟩,
⟨64,370220339,370220571⟩]
theorem checked34535 : checkPrefixCuts (2^48) 4530503681 10 Manual.Count131072.C034535.packed 64 cuts34535 = true := by
 decide +kernel
def pointBounds34535 : List (Nat × Nat × Nat) := [(4530567168,107014257453720,107014641830646)]
theorem point_links_checked34535 : (cuts34535.take 1).map (fun c => (4530503681-1+2*2^10*c.k,107014077654160+c.lower,107014462030975+c.upper)) = pointBounds34535 := by
 decide +kernel
def cuts34536 : List PrefixCut := [⟨37,207813184,207813312⟩,
⟨64,367910895,367911125⟩]
theorem checked34536 : checkPrefixCuts (2^48) 4530634753 10 Manual.Count131072.C034536.packed 64 cuts34536 = true := by
 decide +kernel
def pointBounds34536 : List (Nat × Nat × Nat) := [(4530710528,107014655687683,107015040064858)]
theorem point_links_checked34536 : (cuts34536.take 1).map (fun c => (4530634753-1+2*2^10*c.k,107014447874499+c.lower,107014832251546+c.upper)) = pointBounds34536 := by
 decide +kernel
def cuts34537 : List PrefixCut := [⟨43,248250041,248250200⟩,
⟨64,368521587,368521819⟩]
theorem checked34537 : checkPrefixCuts (2^48) 4530765825 10 Manual.Count131072.C034537.packed 64 cuts34537 = true := by
 decide +kernel
def pointBounds34537 : List (Nat × Nat × Nat) := [(4530853888,107015064035435,107015448412871)]
theorem point_links_checked34537 : (cuts34537.take 1).map (fun c => (4530765825-1+2*2^10*c.k,107014815785394+c.lower,107015200162671+c.upper)) = pointBounds34537 := by
 decide +kernel
def cuts34538 : List PrefixCut := [⟨49,277502298,277502469⟩,
⟨64,361615283,361615507⟩]
theorem checked34538 : checkPrefixCuts (2^48) 4530896897 10 Manual.Count131072.C034538.packed 64 cuts34538 = true := by
 decide +kernel
def pointBounds34538 : List (Nat × Nat × Nat) := [(4530997248,107015461809279,107015846186959)]
theorem point_links_checked34538 : (cuts34538.take 1).map (fun c => (4530896897-1+2*2^10*c.k,107015184306981+c.lower,107015568684490+c.upper)) = pointBounds34538 := by
 decide +kernel
def cuts34539 : List PrefixCut := [⟨55,312343704,312343906⟩,
⟨64,364524482,364524716⟩]
theorem checked34539 : checkPrefixCuts (2^48) 4531027969 10 Manual.Count131072.C034539.packed 64 cuts34539 = true := by
 decide +kernel
def pointBounds34539 : List (Nat × Nat × Nat) := [(4531140608,107015858265968,107016242643903)]
theorem point_links_checked34539 : (cuts34539.take 1).map (fun c => (4531027969-1+2*2^10*c.k,107015545922264+c.lower,107015930299997+c.upper)) = pointBounds34539 := by
 decide +kernel
def cuts34540 : List PrefixCut := [⟨61,344698273,344698488⟩,
⟨64,362215574,362215800⟩]
theorem checked34540 : checkPrefixCuts (2^48) 4531159041 10 Manual.Count131072.C034540.packed 64 cuts34540 = true := by
 decide +kernel
def pointBounds34540 : List (Nat × Nat × Nat) := [(4531283968,107016255145019,107016639523201)]
theorem point_links_checked34540 : (cuts34540.take 1).map (fun c => (4531159041-1+2*2^10*c.k,107015910446746+c.lower,107016294824713+c.upper)) = pointBounds34540 := by
 decide +kernel
def cuts34541 : List PrefixCut := [⟨64,368541015,368541253⟩]
theorem checked34541 : checkPrefixCuts (2^48) 4531290113 10 Manual.Count131072.C034541.packed 64 cuts34541 = true := by
 decide +kernel
def cuts34542 : List PrefixCut := [⟨3,17641003,17641014⟩,
⟨64,363064280,363064512⟩]
theorem checked34542 : checkPrefixCuts (2^48) 4531421185 10 Manual.Count131072.C034542.packed 64 cuts34542 = true := by
 decide +kernel
def pointBounds34542 : List (Nat × Nat × Nat) := [(4531427328,107016658844338,107017043222780)]
theorem point_links_checked34542 : (cuts34542.take 1).map (fun c => (4531421185-1+2*2^10*c.k,107016641203335+c.lower,107017025581766+c.upper)) = pointBounds34542 := by
 decide +kernel
def cuts34543 : List PrefixCut := [⟨9,50809519,50809552⟩,
⟨64,366407843,366408076⟩]
theorem checked34543 : checkPrefixCuts (2^48) 4531552257 10 Manual.Count131072.C034543.packed 64 cuts34543 = true := by
 decide +kernel
def pointBounds34543 : List (Nat × Nat × Nat) := [(4531570688,107017055077134,107017439455830)]
theorem point_links_checked34543 : (cuts34543.take 1).map (fun c => (4531552257-1+2*2^10*c.k,107017004267615+c.lower,107017388646278+c.upper)) = pointBounds34543 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000141
