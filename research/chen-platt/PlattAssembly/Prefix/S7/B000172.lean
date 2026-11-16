import PlattAssemblyKernel
import PlattCertificates.Count131072.C065504
import PlattCertificates.Count131072.C065505
import PlattCertificates.Count131072.C065506
import PlattCertificates.Count131072.C065507
import PlattCertificates.Count131072.C065508
import PlattCertificates.Count131072.C065509
import PlattCertificates.Count131072.C065510
import PlattCertificates.Count131072.C065511
import PlattCertificates.Count131072.C065512
import PlattCertificates.Count131072.C065513
import PlattCertificates.Count131072.C065514
import PlattCertificates.Count131072.C065515
import PlattCertificates.Count131072.C065516
import PlattCertificates.Count131072.C065517
import PlattCertificates.Count131072.C065518
import PlattCertificates.Count131072.C065519
import PlattCertificates.Count131072.C065520
import PlattCertificates.Count131072.C065521
import PlattCertificates.Count131072.C065522
import PlattCertificates.Count131072.C065523
import PlattCertificates.Count131072.C065524
import PlattCertificates.Count131072.C065525
import PlattCertificates.Count131072.C065526
import PlattCertificates.Count131072.C065527
import PlattCertificates.Count131072.C065528
import PlattCertificates.Count131072.C065529
import PlattCertificates.Count131072.C065530
import PlattCertificates.Count131072.C065531
import PlattCertificates.Count131072.C065532
import PlattCertificates.Count131072.C065533
import PlattCertificates.Count131072.C065534
import PlattCertificates.Count131072.C065535
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000172
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts65504 : List PrefixCut := [⟨51,148246018,148246101⟩,
⟨64,184848479,184848585⟩]
theorem checked65504 : checkPrefixCuts (2^48) 8589672449 10 Manual.Count131072.C065504.packed 64 cuts65504 = true := by
 decide +kernel
def pointBounds65504 : List (Nat × Nat × Nat) := [(8589776896,114998597086212,114998986115459)]
theorem point_links_checked65504 : (cuts65504.take 1).map (fun c => (8589672449-1+2*2^10*c.k,114998448840194+c.lower,114998837869358+c.upper)) = pointBounds65504 := by
 decide +kernel
def cuts65505 : List PrefixCut := [⟨64,188974438,188974551⟩]
theorem checked65505 : checkPrefixCuts (2^48) 8589803521 10 Manual.Count131072.C065505.packed 64 cuts65505 = true := by
 decide +kernel
def cuts65506 : List PrefixCut := [⟨55,159710145,159710239⟩,
⟨64,186579517,186579625⟩]
theorem checked65506 : checkPrefixCuts (2^48) 8589934593 10 Manual.Count131072.C065506.packed 64 cuts65506 = true := by
 decide +kernel
def pointBounds65506 : List (Nat × Nat × Nat) := [(8590047232,114998982373256,114999371402733)]
theorem point_links_checked65506 : (cuts65506.take 1).map (fun c => (8589934593-1+2*2^10*c.k,114998822663111+c.lower,114999211692494+c.upper)) = pointBounds65506 := by
 decide +kernel
def cuts65507 : List PrefixCut := [⟨64,187920142,187920250⟩]
theorem checked65507 : checkPrefixCuts (2^48) 8590065665 10 Manual.Count131072.C065507.packed 64 cuts65507 = true := by
 decide +kernel
def cuts65508 : List PrefixCut := [⟨59,171271860,171271961⟩,
⟨64,186606588,186606697⟩]
theorem checked65508 : checkPrefixCuts (2^48) 8590196737 10 Manual.Count131072.C065508.packed 64 cuts65508 = true := by
 decide +kernel
def pointBounds65508 : List (Nat × Nat × Nat) := [(8590317568,114999368434630,114999757464330)]
theorem point_links_checked65508 : (cuts65508.take 1).map (fun c => (8590196737-1+2*2^10*c.k,114999197162770+c.lower,114999586192369+c.upper)) = pointBounds65508 := by
 decide +kernel
def cuts65509 : List PrefixCut := [⟨64,188438663,188438775⟩]
theorem checked65509 : checkPrefixCuts (2^48) 8590327809 10 Manual.Count131072.C065509.packed 64 cuts65509 = true := by
 decide +kernel
def cuts65510 : List PrefixCut := [⟨63,184143489,184143598⟩,
⟨64,187190680,187190791⟩]
theorem checked65510 : checkPrefixCuts (2^48) 8590458881 10 Manual.Count131072.C065510.packed 64 cuts65510 = true := by
 decide +kernel
def pointBounds65510 : List (Nat × Nat × Nat) := [(8590587904,114999756351510,115000145381439)]
theorem point_links_checked65510 : (cuts65510.take 1).map (fun c => (8590458881-1+2*2^10*c.k,114999572208021+c.lower,114999961237841+c.upper)) = pointBounds65510 := by
 decide +kernel
def cuts65511 : List PrefixCut := [⟨64,185811682,185811793⟩]
theorem checked65511 : checkPrefixCuts (2^48) 8590589953 10 Manual.Count131072.C065511.packed 64 cuts65511 = true := by
 decide +kernel
def cuts65512 : List PrefixCut := [⟨64,187709194,187709302⟩]
theorem checked65512 : checkPrefixCuts (2^48) 8590721025 10 Manual.Count131072.C065512.packed 64 cuts65512 = true := by
 decide +kernel
def cuts65513 : List PrefixCut := [⟨3,9042996,9043001⟩,
⟨64,186657890,186658001⟩]
theorem checked65513 : checkPrefixCuts (2^48) 8590852097 10 Manual.Count131072.C065513.packed 64 cuts65513 = true := by
 decide +kernel
def pointBounds65513 : List (Nat × Nat × Nat) := [(8590858240,115000141962573,115000530992728)]
theorem point_links_checked65513 : (cuts65513.take 1).map (fun c => (8590852097-1+2*2^10*c.k,115000132919577+c.lower,115000521949727+c.upper)) = pointBounds65513 := by
 decide +kernel
def cuts65514 : List PrefixCut := [⟨64,189996928,189997040⟩]
theorem checked65514 : checkPrefixCuts (2^48) 8590983169 10 Manual.Count131072.C065514.packed 64 cuts65514 = true := by
 decide +kernel
def cuts65515 : List PrefixCut := [⟨7,20509929,20509941⟩,
⟨64,187176405,187176512⟩]
theorem checked65515 : checkPrefixCuts (2^48) 8591114241 10 Manual.Count131072.C065515.packed 64 cuts65515 = true := by
 decide +kernel
def pointBounds65515 : List (Nat × Nat × Nat) := [(8591128576,115000530084324,115000919114709)]
theorem point_links_checked65515 : (cuts65515.take 1).map (fun c => (8591114241-1+2*2^10*c.k,115000509574395+c.lower,115000898604768+c.upper)) = pointBounds65515 := by
 decide +kernel
def cuts65516 : List PrefixCut := [⟨64,186747614,186747726⟩]
theorem checked65516 : checkPrefixCuts (2^48) 8591245313 10 Manual.Count131072.C065516.packed 64 cuts65516 = true := by
 decide +kernel
def cuts65517 : List PrefixCut := [⟨11,32565875,32565893⟩,
⟨64,184779060,184779164⟩]
theorem checked65517 : checkPrefixCuts (2^48) 8591376385 10 Manual.Count131072.C065517.packed 64 cuts65517 = true := by
 decide +kernel
def pointBounds65517 : List (Nat × Nat × Nat) := [(8591398912,115000916064289,115001305094899)]
theorem point_links_checked65517 : (cuts65517.take 1).map (fun c => (8591376385-1+2*2^10*c.k,115000883498414+c.lower,115001272529006+c.upper)) = pointBounds65517 := by
 decide +kernel
def cuts65518 : List PrefixCut := [⟨64,189035250,189035359⟩]
theorem checked65518 : checkPrefixCuts (2^48) 8591507457 10 Manual.Count131072.C065518.packed 64 cuts65518 = true := by
 decide +kernel
def cuts65519 : List PrefixCut := [⟨15,43638227,43638253⟩,
⟨64,186673561,186673668⟩]
theorem checked65519 : checkPrefixCuts (2^48) 8591638529 10 Manual.Count131072.C065519.packed 64 cuts65519 = true := by
 decide +kernel
def pointBounds65519 : List (Nat × Nat × Nat) := [(8591669248,115001300950951,115001689981782)]
theorem point_links_checked65519 : (cuts65519.take 1).map (fun c => (8591638529-1+2*2^10*c.k,115001257312724+c.lower,115001646343529+c.upper)) = pointBounds65519 := by
 decide +kernel
def cuts65520 : List PrefixCut := [⟨64,188144940,188145052⟩]
theorem checked65520 : checkPrefixCuts (2^48) 8591769601 10 Manual.Count131072.C065520.packed 64 cuts65520 = true := by
 decide +kernel
def cuts65521 : List PrefixCut := [⟨19,56478961,56478996⟩,
⟨64,188731755,188731865⟩]
theorem checked65521 : checkPrefixCuts (2^48) 8591900673 10 Manual.Count131072.C065521.packed 64 cuts65521 = true := by
 decide +kernel
def pointBounds65521 : List (Nat × Nat × Nat) := [(8591939584,115001688610186,115002077641245)]
theorem point_links_checked65521 : (cuts65521.take 1).map (fun c => (8591900673-1+2*2^10*c.k,115001632131225+c.lower,115002021162249+c.upper)) = pointBounds65521 := by
 decide +kernel
def cuts65522 : List PrefixCut := [⟨64,191218613,191218727⟩]
theorem checked65522 : checkPrefixCuts (2^48) 8592031745 10 Manual.Count131072.C065522.packed 64 cuts65522 = true := by
 decide +kernel
def cuts65523 : List PrefixCut := [⟨23,68106800,68106838⟩,
⟨64,189184630,189184738⟩]
theorem checked65523 : checkPrefixCuts (2^48) 8592162817 10 Manual.Count131072.C065523.packed 64 cuts65523 = true := by
 decide +kernel
def pointBounds65523 : List (Nat × Nat × Nat) := [(8592209920,115002080188393,115002469219679)]
theorem point_links_checked65523 : (cuts65523.take 1).map (fun c => (8592162817-1+2*2^10*c.k,115002012081593+c.lower,115002401112841+c.upper)) = pointBounds65523 := by
 decide +kernel
def cuts65524 : List PrefixCut := [⟨64,188002433,188002534⟩]
theorem checked65524 : checkPrefixCuts (2^48) 8592293889 10 Manual.Count131072.C065524.packed 64 cuts65524 = true := by
 decide +kernel
def cuts65525 : List PrefixCut := [⟨27,80814945,80814988⟩,
⟨64,189965065,189965170⟩]
theorem checked65525 : checkPrefixCuts (2^48) 8592424961 10 Manual.Count131072.C065525.packed 64 cuts65525 = true := by
 decide +kernel
def pointBounds65525 : List (Nat × Nat × Nat) := [(8592480256,115002470083601,115002859115101)]
theorem point_links_checked65525 : (cuts65525.take 1).map (fun c => (8592424961-1+2*2^10*c.k,115002389268656+c.lower,115002778300113+c.upper)) = pointBounds65525 := by
 decide +kernel
def cuts65526 : List PrefixCut := [⟨64,190093190,190093300⟩]
theorem checked65526 : checkPrefixCuts (2^48) 8592556033 10 Manual.Count131072.C065526.packed 64 cuts65526 = true := by
 decide +kernel
def cuts65527 : List PrefixCut := [⟨31,90901711,90901760⟩,
⟨64,189467898,189468003⟩]
theorem checked65527 : checkPrefixCuts (2^48) 8592687105 10 Manual.Count131072.C065527.packed 64 cuts65527 = true := by
 decide +kernel
def pointBounds65527 : List (Nat × Nat × Nat) := [(8592750592,115002860228622,115003249260343)]
theorem point_links_checked65527 : (cuts65527.take 1).map (fun c => (8592687105-1+2*2^10*c.k,115002769326911+c.lower,115003158358583+c.upper)) = pointBounds65527 := by
 decide +kernel
def cuts65528 : List PrefixCut := [⟨64,189301226,189301341⟩]
theorem checked65528 : checkPrefixCuts (2^48) 8592818177 10 Manual.Count131072.C065528.packed 64 cuts65528 = true := by
 decide +kernel
def cuts65529 : List PrefixCut := [⟨35,103018742,103018800⟩,
⟨64,189462110,189462220⟩]
theorem checked65529 : checkPrefixCuts (2^48) 8592949249 10 Manual.Count131072.C065529.packed 64 cuts65529 = true := by
 decide +kernel
def pointBounds65529 : List (Nat × Nat × Nat) := [(8593020928,115003251114777,115003640146727)]
theorem point_links_checked65529 : (cuts65529.take 1).map (fun c => (8592949249-1+2*2^10*c.k,115003148096035+c.lower,115003537127927+c.upper)) = pointBounds65529 := by
 decide +kernel
def cuts65530 : List PrefixCut := [⟨64,186707746,186707852⟩]
theorem checked65530 : checkPrefixCuts (2^48) 8593080321 10 Manual.Count131072.C065530.packed 64 cuts65530 = true := by
 decide +kernel
def cuts65531 : List PrefixCut := [⟨39,114414414,114414477⟩,
⟨64,188146130,188146238⟩]
theorem checked65531 : checkPrefixCuts (2^48) 8593211393 10 Manual.Count131072.C065531.packed 64 cuts65531 = true := by
 decide +kernel
def pointBounds65531 : List (Nat × Nat × Nat) := [(8593291264,115003638680305,115004027712476)]
theorem point_links_checked65531 : (cuts65531.take 1).map (fun c => (8593211393-1+2*2^10*c.k,115003524265891+c.lower,115003913297999+c.upper)) = pointBounds65531 := by
 decide +kernel
def cuts65532 : List PrefixCut := [⟨64,187160610,187160716⟩]
theorem checked65532 : checkPrefixCuts (2^48) 8593342465 10 Manual.Count131072.C065532.packed 64 cuts65532 = true := by
 decide +kernel
def cuts65533 : List PrefixCut := [⟨43,126792006,126792076⟩,
⟨64,187976627,187976730⟩]
theorem checked65533 : checkPrefixCuts (2^48) 8593473537 10 Manual.Count131072.C065533.packed 64 cuts65533 = true := by
 decide +kernel
def pointBounds65533 : List (Nat × Nat × Nat) := [(8593561600,115004026364637,115004415397029)]
theorem point_links_checked65533 : (cuts65533.take 1).map (fun c => (8593473537-1+2*2^10*c.k,115003899572631+c.lower,115004288604953+c.upper)) = pointBounds65533 := by
 decide +kernel
def cuts65534 : List PrefixCut := [⟨64,189120137,189120246⟩]
theorem checked65534 : checkPrefixCuts (2^48) 8593604609 10 Manual.Count131072.C065534.packed 64 cuts65534 = true := by
 decide +kernel
def cuts65535 : List PrefixCut := [⟨47,138153480,138153564⟩,
⟨64,187807126,187807238⟩]
theorem checked65535 : checkPrefixCuts (2^48) 8593735681 10 Manual.Count131072.C065535.packed 64 cuts65535 = true := by
 decide +kernel
def pointBounds65535 : List (Nat × Nat × Nat) := [(8593831936,115004414822875,115004803855493)]
theorem point_links_checked65535 : (cuts65535.take 1).map (fun c => (8593735681-1+2*2^10*c.k,115004276669395+c.lower,115004665701929+c.upper)) = pointBounds65535 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000172
