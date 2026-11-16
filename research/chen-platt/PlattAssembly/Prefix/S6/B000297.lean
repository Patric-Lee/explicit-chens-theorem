import PlattAssemblyKernel
import PlattCertificates.Count131072.C059504
import PlattCertificates.Count131072.C059505
import PlattCertificates.Count131072.C059506
import PlattCertificates.Count131072.C059507
import PlattCertificates.Count131072.C059508
import PlattCertificates.Count131072.C059509
import PlattCertificates.Count131072.C059510
import PlattCertificates.Count131072.C059511
import PlattCertificates.Count131072.C059512
import PlattCertificates.Count131072.C059513
import PlattCertificates.Count131072.C059514
import PlattCertificates.Count131072.C059515
import PlattCertificates.Count131072.C059516
import PlattCertificates.Count131072.C059517
import PlattCertificates.Count131072.C059518
import PlattCertificates.Count131072.C059519
import PlattCertificates.Count131072.C059520
import PlattCertificates.Count131072.C059521
import PlattCertificates.Count131072.C059522
import PlattCertificates.Count131072.C059523
import PlattCertificates.Count131072.C059524
import PlattCertificates.Count131072.C059525
import PlattCertificates.Count131072.C059526
import PlattCertificates.Count131072.C059527
import PlattCertificates.Count131072.C059528
import PlattCertificates.Count131072.C059529
import PlattCertificates.Count131072.C059530
import PlattCertificates.Count131072.C059531
import PlattCertificates.Count131072.C059532
import PlattCertificates.Count131072.C059533
import PlattCertificates.Count131072.C059534
import PlattCertificates.Count131072.C059535
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000297
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts59504 : List PrefixCut := [⟨64,210295310,210295429⟩]
theorem checked59504 : checkPrefixCuts (2^48) 7803240449 10 Manual.Count131072.C059504.packed 64 cuts59504 = true := by
 decide +kernel
def cuts59505 : List PrefixCut := [⟨39,125995133,125995205⟩,
⟨64,208740736,208740858⟩]
theorem checked59505 : checkPrefixCuts (2^48) 7803371521 10 Manual.Count131072.C059505.packed 64 cuts59505 = true := by
 decide +kernel
def pointBounds59505 : List (Nat × Nat × Nat) := [(7803451392,113814594858360,113814983207280)]
theorem point_links_checked59505 : (cuts59505.take 1).map (fun c => (7803371521-1+2*2^10*c.k,113814468863227+c.lower,113814857212075+c.upper)) = pointBounds59505 := by
 decide +kernel
def cuts59506 : List PrefixCut := [⟨64,209025786,209025902⟩]
theorem checked59506 : checkPrefixCuts (2^48) 7803502593 10 Manual.Count131072.C059506.packed 64 cuts59506 = true := by
 decide +kernel
def cuts59507 : List PrefixCut := [⟨31,99732375,99732434⟩,
⟨64,207471292,207471412⟩]
theorem checked59507 : checkPrefixCuts (2^48) 7803633665 10 Manual.Count131072.C059507.packed 64 cuts59507 = true := by
 decide +kernel
def pointBounds59507 : List (Nat × Nat × Nat) := [(7803697152,113814986362124,113815374711269)]
theorem point_links_checked59507 : (cuts59507.take 1).map (fun c => (7803633665-1+2*2^10*c.k,113814886629749+c.lower,113815274978835+c.upper)) = pointBounds59507 := by
 decide +kernel
def cuts59508 : List PrefixCut := [⟨64,208044918,208045034⟩]
theorem checked59508 : checkPrefixCuts (2^48) 7803764737 10 Manual.Count131072.C059508.packed 64 cuts59508 = true := by
 decide +kernel
def cuts59509 : List PrefixCut := [⟨23,75022274,75022317⟩,
⟨64,210494051,210494172⟩]
theorem checked59509 : checkPrefixCuts (2^48) 7803895809 10 Manual.Count131072.C059509.packed 64 cuts59509 = true := by
 decide +kernel
def pointBounds59509 : List (Nat × Nat × Nat) := [(7803942912,113815377168233,113815765517598)]
theorem point_links_checked59509 : (cuts59509.take 1).map (fun c => (7803895809-1+2*2^10*c.k,113815302145959+c.lower,113815690495281+c.upper)) = pointBounds59509 := by
 decide +kernel
def cuts59510 : List PrefixCut := [⟨64,205404977,205405093⟩]
theorem checked59510 : checkPrefixCuts (2^48) 7804026881 10 Manual.Count131072.C059510.packed 64 cuts59510 = true := by
 decide +kernel
def cuts59511 : List PrefixCut := [⟨15,48943229,48943257⟩,
⟨64,206339280,206339396⟩]
theorem checked59511 : checkPrefixCuts (2^48) 7804157953 10 Manual.Count131072.C059511.packed 64 cuts59511 = true := by
 decide +kernel
def pointBounds59511 : List (Nat × Nat × Nat) := [(7804188672,113815766988216,113816155337803)]
theorem point_links_checked59511 : (cuts59511.take 1).map (fun c => (7804157953-1+2*2^10*c.k,113815718044987+c.lower,113816106394546+c.upper)) = pointBounds59511 := by
 decide +kernel
def cuts59512 : List PrefixCut := [⟨64,205578423,205578543⟩]
theorem checked59512 : checkPrefixCuts (2^48) 7804289025 10 Manual.Count131072.C059512.packed 64 cuts59512 = true := by
 decide +kernel
def cuts59513 : List PrefixCut := [⟨7,24164255,24164268⟩,
⟨64,206115976,206116094⟩]
theorem checked59513 : checkPrefixCuts (2^48) 7804420097 10 Manual.Count131072.C059513.packed 64 cuts59513 = true := by
 decide +kernel
def pointBounds59513 : List (Nat × Nat × Nat) := [(7804434432,113816154126945,113816542476753)]
theorem point_links_checked59513 : (cuts59513.take 1).map (fun c => (7804420097-1+2*2^10*c.k,113816129962690+c.lower,113816518312485+c.upper)) = pointBounds59513 := by
 decide +kernel
def cuts59514 : List PrefixCut := [⟨63,204201072,204201188⟩,
⟨64,207338717,207338834⟩]
theorem checked59514 : checkPrefixCuts (2^48) 7804551169 10 Manual.Count131072.C059514.packed 64 cuts59514 = true := by
 decide +kernel
def pointBounds59514 : List (Nat × Nat × Nat) := [(7804680192,113816540279738,113816928629767)]
theorem point_links_checked59514 : (cuts59514.take 1).map (fun c => (7804551169-1+2*2^10*c.k,113816336078666+c.lower,113816724428579+c.upper)) = pointBounds59514 := by
 decide +kernel
def cuts59515 : List PrefixCut := [⟨64,208886011,208886129⟩]
theorem checked59515 : checkPrefixCuts (2^48) 7804682241 10 Manual.Count131072.C059515.packed 64 cuts59515 = true := by
 decide +kernel
def cuts59516 : List PrefixCut := [⟨55,176352998,176353099⟩,
⟨64,206358003,206358120⟩]
theorem checked59516 : checkPrefixCuts (2^48) 7804813313 10 Manual.Count131072.C059516.packed 64 cuts59516 = true := by
 decide +kernel
def pointBounds59516 : List (Nat × Nat × Nat) := [(7804925952,113816928656392,113817317006641)]
theorem point_links_checked59516 : (cuts59516.take 1).map (fun c => (7804813313-1+2*2^10*c.k,113816752303394+c.lower,113817140653542+c.upper)) = pointBounds59516 := by
 decide +kernel
def cuts59517 : List PrefixCut := [⟨64,205236585,205236705⟩]
theorem checked59517 : checkPrefixCuts (2^48) 7804944385 10 Manual.Count131072.C059517.packed 64 cuts59517 = true := by
 decide +kernel
def cuts59518 : List PrefixCut := [⟨47,150562352,150562435⟩,
⟨64,205485592,205485708⟩]
theorem checked59518 : checkPrefixCuts (2^48) 7805075457 10 Manual.Count131072.C059518.packed 64 cuts59518 = true := by
 decide +kernel
def pointBounds59518 : List (Nat × Nat × Nat) := [(7805171712,113817314460334,113817702810802)]
theorem point_links_checked59518 : (cuts59518.take 1).map (fun c => (7805075457-1+2*2^10*c.k,113817163897982+c.lower,113817552248367+c.upper)) = pointBounds59518 := by
 decide +kernel
def cuts59519 : List PrefixCut := [⟨64,207573732,207573850⟩]
theorem checked59519 : checkPrefixCuts (2^48) 7805206529 10 Manual.Count131072.C059519.packed 64 cuts59519 = true := by
 decide +kernel
def cuts59520 : List PrefixCut := [⟨39,128884391,128884464⟩,
⟨64,209553655,209553770⟩]
theorem checked59520 : checkPrefixCuts (2^48) 7805337601 10 Manual.Count131072.C059520.packed 64 cuts59520 = true := by
 decide +kernel
def pointBounds59520 : List (Nat × Nat × Nat) := [(7805417472,113817705841697,113818094192389)]
theorem point_links_checked59520 : (cuts59520.take 1).map (fun c => (7805337601-1+2*2^10*c.k,113817576957306+c.lower,113817965307925+c.upper)) = pointBounds59520 := by
 decide +kernel
def cuts59521 : List PrefixCut := [⟨64,209514051,209514171⟩]
theorem checked59521 : checkPrefixCuts (2^48) 7805468673 10 Manual.Count131072.C059521.packed 64 cuts59521 = true := by
 decide +kernel
def cuts59522 : List PrefixCut := [⟨31,99851492,99851549⟩,
⟨64,206553587,206553708⟩]
theorem checked59522 : checkPrefixCuts (2^48) 7805599745 10 Manual.Count131072.C059522.packed 64 cuts59522 = true := by
 decide +kernel
def pointBounds59522 : List (Nat × Nat × Nat) := [(7805663232,113818095876504,113818484227415)]
theorem point_links_checked59522 : (cuts59522.take 1).map (fun c => (7805599745-1+2*2^10*c.k,113817996025012+c.lower,113818384375866+c.upper)) = pointBounds59522 := by
 decide +kernel
def cuts59523 : List PrefixCut := [⟨64,207415552,207415670⟩]
theorem checked59523 : checkPrefixCuts (2^48) 7805730817 10 Manual.Count131072.C059523.packed 64 cuts59523 = true := by
 decide +kernel
def cuts59524 : List PrefixCut := [⟨23,75760625,75760669⟩,
⟨64,211667052,211667173⟩]
theorem checked59524 : checkPrefixCuts (2^48) 7805861889 10 Manual.Count131072.C059524.packed 64 cuts59524 = true := by
 decide +kernel
def pointBounds59524 : List (Nat × Nat × Nat) := [(7805908992,113818485754776,113818874105913)]
theorem point_links_checked59524 : (cuts59524.take 1).map (fun c => (7805861889-1+2*2^10*c.k,113818409994151+c.lower,113818798345244+c.upper)) = pointBounds59524 := by
 decide +kernel
def cuts59525 : List PrefixCut := [⟨64,206002302,206002418⟩]
theorem checked59525 : checkPrefixCuts (2^48) 7805992961 10 Manual.Count131072.C059525.packed 64 cuts59525 = true := by
 decide +kernel
def cuts59526 : List PrefixCut := [⟨15,48534262,48534289⟩,
⟨64,208595017,208595134⟩]
theorem checked59526 : checkPrefixCuts (2^48) 7806124033 10 Manual.Count131072.C059526.packed 64 cuts59526 = true := by
 decide +kernel
def pointBounds59526 : List (Nat × Nat × Nat) := [(7806154752,113818876197767,113819264549124)]
theorem point_links_checked59526 : (cuts59526.take 1).map (fun c => (7806124033-1+2*2^10*c.k,113818827663505+c.lower,113819216014835+c.upper)) = pointBounds59526 := by
 decide +kernel
def cuts59527 : List PrefixCut := [⟨64,209348731,209348851⟩]
theorem checked59527 : checkPrefixCuts (2^48) 7806255105 10 Manual.Count131072.C059527.packed 64 cuts59527 = true := by
 decide +kernel
def cuts59528 : List PrefixCut := [⟨7,22319265,22319278⟩,
⟨64,203179512,203179630⟩]
theorem checked59528 : checkPrefixCuts (2^48) 7806386177 10 Manual.Count131072.C059528.packed 64 cuts59528 = true := by
 decide +kernel
def pointBounds59528 : List (Nat × Nat × Nat) := [(7806400512,113819267926518,113819656278098)]
theorem point_links_checked59528 : (cuts59528.take 1).map (fun c => (7806386177-1+2*2^10*c.k,113819245607253+c.lower,113819633958820+c.upper)) = pointBounds59528 := by
 decide +kernel
def cuts59529 : List PrefixCut := [⟨63,204906821,204906944⟩,
⟨64,208079731,208079856⟩]
theorem checked59529 : checkPrefixCuts (2^48) 7806517249 10 Manual.Count131072.C059529.packed 64 cuts59529 = true := by
 decide +kernel
def pointBounds59529 : List (Nat × Nat × Nat) := [(7806646272,113819653693586,113820042045394)]
theorem point_links_checked59529 : (cuts59529.take 1).map (fun c => (7806517249-1+2*2^10*c.k,113819448786765+c.lower,113819837138450+c.upper)) = pointBounds59529 := by
 decide +kernel
def cuts59530 : List PrefixCut := [⟨64,207030628,207030749⟩]
theorem checked59530 : checkPrefixCuts (2^48) 7806648321 10 Manual.Count131072.C059530.packed 64 cuts59530 = true := by
 decide +kernel
def cuts59531 : List PrefixCut := [⟨55,181031797,181031900⟩,
⟨64,208721749,208721867⟩]
theorem checked59531 : checkPrefixCuts (2^48) 7806779393 10 Manual.Count131072.C059531.packed 64 cuts59531 = true := by
 decide +kernel
def pointBounds59531 : List (Nat × Nat × Nat) := [(7806892032,113820044928921,113820433280955)]
theorem point_links_checked59531 : (cuts59531.take 1).map (fun c => (7806779393-1+2*2^10*c.k,113819863897124+c.lower,113820252249055+c.upper)) = pointBounds59531 := by
 decide +kernel
def cuts59532 : List PrefixCut := [⟨64,207131851,207131965⟩]
theorem checked59532 : checkPrefixCuts (2^48) 7806910465 10 Manual.Count131072.C059532.packed 64 cuts59532 = true := by
 decide +kernel
def cuts59533 : List PrefixCut := [⟨47,152651603,152651691⟩,
⟨64,206407302,206407420⟩]
theorem checked59533 : checkPrefixCuts (2^48) 7807041537 10 Manual.Count131072.C059533.packed 64 cuts59533 = true := by
 decide +kernel
def pointBounds59533 : List (Nat × Nat × Nat) := [(7807137792,113820432402327,113820820754578)]
theorem point_links_checked59533 : (cuts59533.take 1).map (fun c => (7807041537-1+2*2^10*c.k,113820279750724+c.lower,113820668102887+c.upper)) = pointBounds59533 := by
 decide +kernel
def cuts59534 : List PrefixCut := [⟨64,208530956,208531074⟩]
theorem checked59534 : checkPrefixCuts (2^48) 7807172609 10 Manual.Count131072.C059534.packed 64 cuts59534 = true := by
 decide +kernel
def cuts59535 : List PrefixCut := [⟨39,125931675,125931748⟩,
⟨64,205715370,205715490⟩]
theorem checked59535 : checkPrefixCuts (2^48) 7807303681 10 Manual.Count131072.C059535.packed 64 cuts59535 = true := by
 decide +kernel
def pointBounds59535 : List (Nat × Nat × Nat) := [(7807383552,113820820620657,113821208973129)]
theorem point_links_checked59535 : (cuts59535.take 1).map (fun c => (7807303681-1+2*2^10*c.k,113820694688982+c.lower,113821083041381+c.upper)) = pointBounds59535 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000297
