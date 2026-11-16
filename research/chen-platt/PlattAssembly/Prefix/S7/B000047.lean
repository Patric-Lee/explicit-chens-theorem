import PlattAssemblyKernel
import PlattCertificates.Count131072.C061504
import PlattCertificates.Count131072.C061505
import PlattCertificates.Count131072.C061506
import PlattCertificates.Count131072.C061507
import PlattCertificates.Count131072.C061508
import PlattCertificates.Count131072.C061509
import PlattCertificates.Count131072.C061510
import PlattCertificates.Count131072.C061511
import PlattCertificates.Count131072.C061512
import PlattCertificates.Count131072.C061513
import PlattCertificates.Count131072.C061514
import PlattCertificates.Count131072.C061515
import PlattCertificates.Count131072.C061516
import PlattCertificates.Count131072.C061517
import PlattCertificates.Count131072.C061518
import PlattCertificates.Count131072.C061519
import PlattCertificates.Count131072.C061520
import PlattCertificates.Count131072.C061521
import PlattCertificates.Count131072.C061522
import PlattCertificates.Count131072.C061523
import PlattCertificates.Count131072.C061524
import PlattCertificates.Count131072.C061525
import PlattCertificates.Count131072.C061526
import PlattCertificates.Count131072.C061527
import PlattCertificates.Count131072.C061528
import PlattCertificates.Count131072.C061529
import PlattCertificates.Count131072.C061530
import PlattCertificates.Count131072.C061531
import PlattCertificates.Count131072.C061532
import PlattCertificates.Count131072.C061533
import PlattCertificates.Count131072.C061534
import PlattCertificates.Count131072.C061535
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000047
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts61504 : List PrefixCut := [⟨64,200319400,200319512⟩]
theorem checked61504 : checkPrefixCuts (2^48) 8065384449 10 Manual.Count131072.C061504.packed 64 cuts61504 = true := by
 decide +kernel
def cuts61505 : List PrefixCut := [⟨40,125110707,125110781⟩,
⟨64,198222231,198222351⟩]
theorem checked61505 : checkPrefixCuts (2^48) 8065515521 10 Manual.Count131072.C061505.packed 64 cuts61505 = true := by
 decide +kernel
def pointBounds61505 : List (Nat × Nat × Nat) := [(8065597440,114222663888801,114223052470978)]
theorem point_links_checked61505 : (cuts61505.take 1).map (fun c => (8065515521-1+2*2^10*c.k,114222538778094+c.lower,114222927360197+c.upper)) = pointBounds61505 := by
 decide +kernel
def cuts61506 : List PrefixCut := [⟨64,202336936,202337053⟩]
theorem checked61506 : checkPrefixCuts (2^48) 8065646593 10 Manual.Count131072.C061506.packed 64 cuts61506 = true := by
 decide +kernel
def cuts61507 : List PrefixCut := [⟨36,115160983,115161050⟩,
⟨64,200798186,200798302⟩]
theorem checked61507 : checkPrefixCuts (2^48) 8065777665 10 Manual.Count131072.C061507.packed 64 cuts61507 = true := by
 decide +kernel
def pointBounds61507 : List (Nat × Nat × Nat) := [(8065851392,114223054498244,114223443080651)]
theorem point_links_checked61507 : (cuts61507.take 1).map (fun c => (8065777665-1+2*2^10*c.k,114222939337261+c.lower,114223327919601+c.upper)) = pointBounds61507 := by
 decide +kernel
def cuts61508 : List PrefixCut := [⟨64,201248560,201248672⟩]
theorem checked61508 : checkPrefixCuts (2^48) 8065908737 10 Manual.Count131072.C061508.packed 64 cuts61508 = true := by
 decide +kernel
def cuts61509 : List PrefixCut := [⟨32,100047268,100047324⟩,
⟨64,200198411,200198521⟩]
theorem checked61509 : checkPrefixCuts (2^48) 8066039809 10 Manual.Count131072.C061509.packed 64 cuts61509 = true := by
 decide +kernel
def pointBounds61509 : List (Nat × Nat × Nat) := [(8066105344,114223441431275,114223830013899)]
theorem point_links_checked61509 : (cuts61509.take 1).map (fun c => (8066039809-1+2*2^10*c.k,114223341384007+c.lower,114223729966575+c.upper)) = pointBounds61509 := by
 decide +kernel
def cuts61510 : List PrefixCut := [⟨64,199846215,199846334⟩]
theorem checked61510 : checkPrefixCuts (2^48) 8066170881 10 Manual.Count131072.C061510.packed 64 cuts61510 = true := by
 decide +kernel
def cuts61511 : List PrefixCut := [⟨28,89296399,89296451⟩,
⟨64,201762189,201762304⟩]
theorem checked61511 : checkPrefixCuts (2^48) 8066301953 10 Manual.Count131072.C061511.packed 64 cuts61511 = true := by
 decide +kernel
def pointBounds61511 : List (Nat × Nat × Nat) := [(8066359296,114223830725032,114224219307881)]
theorem point_links_checked61511 : (cuts61511.take 1).map (fun c => (8066301953-1+2*2^10*c.k,114223741428633+c.lower,114224130011430+c.upper)) = pointBounds61511 := by
 decide +kernel
def cuts61512 : List PrefixCut := [⟨64,201898465,201898581⟩]
theorem checked61512 : checkPrefixCuts (2^48) 8066433025 10 Manual.Count131072.C061512.packed 64 cuts61512 = true := by
 decide +kernel
def cuts61513 : List PrefixCut := [⟨24,76836408,76836452⟩,
⟨64,205454350,205454466⟩]
theorem checked61513 : checkPrefixCuts (2^48) 8066564097 10 Manual.Count131072.C061513.packed 64 cuts61513 = true := by
 decide +kernel
def pointBounds61513 : List (Nat × Nat × Nat) := [(8066613248,114224221925695,114224610508767)]
theorem point_links_checked61513 : (cuts61513.take 1).map (fun c => (8066564097-1+2*2^10*c.k,114224145089287+c.lower,114224533672315+c.upper)) = pointBounds61513 := by
 decide +kernel
def cuts61514 : List PrefixCut := [⟨64,202694461,202694573⟩]
theorem checked61514 : checkPrefixCuts (2^48) 8066695169 10 Manual.Count131072.C061514.packed 64 cuts61514 = true := by
 decide +kernel
def cuts61515 : List PrefixCut := [⟨20,63539791,63539827⟩,
⟨64,199446153,199446263⟩]
theorem checked61515 : checkPrefixCuts (2^48) 8066826241 10 Manual.Count131072.C061515.packed 64 cuts61515 = true := by
 decide +kernel
def pointBounds61515 : List (Nat × Nat × Nat) := [(8066867200,114224616777889,114225005361181)]
theorem point_links_checked61515 : (cuts61515.take 1).map (fun c => (8066826241-1+2*2^10*c.k,114224553238098+c.lower,114224941821354+c.upper)) = pointBounds61515 := by
 decide +kernel
def cuts61516 : List PrefixCut := [⟨64,201606212,201606327⟩]
theorem checked61516 : checkPrefixCuts (2^48) 8066957313 10 Manual.Count131072.C061516.packed 64 cuts61516 = true := by
 decide +kernel
def cuts61517 : List PrefixCut := [⟨16,48115636,48115667⟩,
⟨64,199265201,199265317⟩]
theorem checked61517 : checkPrefixCuts (2^48) 8067088385 10 Manual.Count131072.C061517.packed 64 cuts61517 = true := by
 decide +kernel
def pointBounds61517 : List (Nat × Nat × Nat) := [(8067121152,114225002406099,114225390989611)]
theorem point_links_checked61517 : (cuts61517.take 1).map (fun c => (8067088385-1+2*2^10*c.k,114224954290463+c.lower,114225342873944+c.upper)) = pointBounds61517 := by
 decide +kernel
def cuts61518 : List PrefixCut := [⟨64,199750454,199750566⟩]
theorem checked61518 : checkPrefixCuts (2^48) 8067219457 10 Manual.Count131072.C061518.packed 64 cuts61518 = true := by
 decide +kernel
def cuts61519 : List PrefixCut := [⟨12,39077438,39077461⟩,
⟨64,201456837,201456954⟩]
theorem checked61519 : checkPrefixCuts (2^48) 8067350529 10 Manual.Count131072.C061519.packed 64 cuts61519 = true := by
 decide +kernel
def pointBounds61519 : List (Nat × Nat × Nat) := [(8067375104,114225392383556,114225780967288)]
theorem point_links_checked61519 : (cuts61519.take 1).map (fun c => (8067350529-1+2*2^10*c.k,114225353306118+c.lower,114225741889827+c.upper)) = pointBounds61519 := by
 decide +kernel
def cuts61520 : List PrefixCut := [⟨64,199360160,199360275⟩]
theorem checked61520 : checkPrefixCuts (2^48) 8067481601 10 Manual.Count131072.C061520.packed 64 cuts61520 = true := by
 decide +kernel
def cuts61521 : List PrefixCut := [⟨8,25992644,25992658⟩,
⟨64,204904332,204904438⟩]
theorem checked61521 : checkPrefixCuts (2^48) 8067612673 10 Manual.Count131072.C061521.packed 64 cuts61521 = true := by
 decide +kernel
def pointBounds61521 : List (Nat × Nat × Nat) := [(8067629056,114225780115759,114226168699714)]
theorem point_links_checked61521 : (cuts61521.take 1).map (fun c => (8067612673-1+2*2^10*c.k,114225754123115+c.lower,114226142707056+c.upper)) = pointBounds61521 := by
 decide +kernel
def cuts61522 : List PrefixCut := [⟨64,197993026,197993142⟩]
theorem checked61522 : checkPrefixCuts (2^48) 8067743745 10 Manual.Count131072.C061522.packed 64 cuts61522 = true := by
 decide +kernel
def cuts61523 : List PrefixCut := [⟨4,12210919,12210925⟩,
⟨64,198513143,198513257⟩]
theorem checked61523 : checkPrefixCuts (2^48) 8067874817 10 Manual.Count131072.C061523.packed 64 cuts61523 = true := by
 decide +kernel
def pointBounds61523 : List (Nat × Nat × Nat) := [(8067883008,114226169231392,114226557815561)]
theorem point_links_checked61523 : (cuts61523.take 1).map (fun c => (8067874817-1+2*2^10*c.k,114226157020473+c.lower,114226545604636+c.upper)) = pointBounds61523 := by
 decide +kernel
def cuts61524 : List PrefixCut := [⟨64,200010071,200010191⟩]
theorem checked61524 : checkPrefixCuts (2^48) 8068005889 10 Manual.Count131072.C061524.packed 64 cuts61524 = true := by
 decide +kernel
def pointBounds61524 : List (Nat × Nat × Nat) := [(8068136960,114226555543687,114226944128084)]
theorem point_links_checked61524 : (cuts61524.take 1).map (fun c => (8068005889-1+2*2^10*c.k,114226355533616+c.lower,114226744117893+c.upper)) = pointBounds61524 := by
 decide +kernel
def cuts61525 : List PrefixCut := [⟨64,202065157,202065280⟩]
theorem checked61525 : checkPrefixCuts (2^48) 8068136961 10 Manual.Count131072.C061525.packed 64 cuts61525 = true := by
 decide +kernel
def cuts61526 : List PrefixCut := [⟨60,188107415,188107525⟩,
⟨64,201399022,201399140⟩]
theorem checked61526 : checkPrefixCuts (2^48) 8068268033 10 Manual.Count131072.C061526.packed 64 cuts61526 = true := by
 decide +kernel
def pointBounds61526 : List (Nat × Nat × Nat) := [(8068390912,114226945716259,114227334300889)]
theorem point_links_checked61526 : (cuts61526.take 1).map (fun c => (8068268033-1+2*2^10*c.k,114226757608844+c.lower,114227146193364+c.upper)) = pointBounds61526 := by
 decide +kernel
def cuts61527 : List PrefixCut := [⟨64,199023512,199023625⟩]
theorem checked61527 : checkPrefixCuts (2^48) 8068399105 10 Manual.Count131072.C061527.packed 64 cuts61527 = true := by
 decide +kernel
def cuts61528 : List PrefixCut := [⟨56,172926295,172926400⟩,
⟨64,198322569,198322688⟩]
theorem checked61528 : checkPrefixCuts (2^48) 8068530177 10 Manual.Count131072.C061528.packed 64 cuts61528 = true := by
 decide +kernel
def pointBounds61528 : List (Nat × Nat × Nat) := [(8068644864,114227330957673,114227719542529)]
theorem point_links_checked61528 : (cuts61528.take 1).map (fun c => (8068530177-1+2*2^10*c.k,114227158031378+c.lower,114227546616129+c.upper)) = pointBounds61528 := by
 decide +kernel
def cuts61529 : List PrefixCut := [⟨64,198807763,198807872⟩]
theorem checked61529 : checkPrefixCuts (2^48) 8068661249 10 Manual.Count131072.C061529.packed 64 cuts61529 = true := by
 decide +kernel
def cuts61530 : List PrefixCut := [⟨52,162350868,162350962⟩,
⟨64,199432428,199432544⟩]
theorem checked61530 : checkPrefixCuts (2^48) 8068792321 10 Manual.Count131072.C061530.packed 64 cuts61530 = true := by
 decide +kernel
def pointBounds61530 : List (Nat × Nat × Nat) := [(8068898816,114227717512578,114228106097651)]
theorem point_links_checked61530 : (cuts61530.take 1).map (fun c => (8068792321-1+2*2^10*c.k,114227555161710+c.lower,114227943746689+c.upper)) = pointBounds61530 := by
 decide +kernel
def cuts61531 : List PrefixCut := [⟨64,200126866,200126980⟩]
theorem checked61531 : checkPrefixCuts (2^48) 8068923393 10 Manual.Count131072.C061531.packed 64 cuts61531 = true := by
 decide +kernel
def cuts61532 : List PrefixCut := [⟨48,151008698,151008788⟩,
⟨64,200891047,200891166⟩]
theorem checked61532 : checkPrefixCuts (2^48) 8069054465 10 Manual.Count131072.C061532.packed 64 cuts61532 = true := by
 decide +kernel
def pointBounds61532 : List (Nat × Nat × Nat) := [(8069152768,114228105729702,114228494315001)]
theorem point_links_checked61532 : (cuts61532.take 1).map (fun c => (8069054465-1+2*2^10*c.k,114227954721004+c.lower,114228343306213+c.upper)) = pointBounds61532 := by
 decide +kernel
def cuts61533 : List PrefixCut := [⟨64,199422722,199422842⟩]
theorem checked61533 : checkPrefixCuts (2^48) 8069185537 10 Manual.Count131072.C061533.packed 64 cuts61533 = true := by
 decide +kernel
def cuts61534 : List PrefixCut := [⟨44,135132578,135132661⟩,
⟨64,198093948,198094066⟩]
theorem checked61534 : checkPrefixCuts (2^48) 8069316609 10 Manual.Count131072.C061534.packed 64 cuts61534 = true := by
 decide +kernel
def pointBounds61534 : List (Nat × Nat × Nat) := [(8069406720,114228490167351,114228878752882)]
theorem point_links_checked61534 : (cuts61534.take 1).map (fun c => (8069316609-1+2*2^10*c.k,114228355034773+c.lower,114228743620221+c.upper)) = pointBounds61534 := by
 decide +kernel
def cuts61535 : List PrefixCut := [⟨64,201125430,201125544⟩]
theorem checked61535 : checkPrefixCuts (2^48) 8069447681 10 Manual.Count131072.C061535.packed 64 cuts61535 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000047
