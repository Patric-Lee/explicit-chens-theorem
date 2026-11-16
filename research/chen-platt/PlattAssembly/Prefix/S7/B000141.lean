import PlattAssemblyKernel
import PlattCertificates.Count131072.C064512
import PlattCertificates.Count131072.C064513
import PlattCertificates.Count131072.C064514
import PlattCertificates.Count131072.C064515
import PlattCertificates.Count131072.C064516
import PlattCertificates.Count131072.C064517
import PlattCertificates.Count131072.C064518
import PlattCertificates.Count131072.C064519
import PlattCertificates.Count131072.C064520
import PlattCertificates.Count131072.C064521
import PlattCertificates.Count131072.C064522
import PlattCertificates.Count131072.C064523
import PlattCertificates.Count131072.C064524
import PlattCertificates.Count131072.C064525
import PlattCertificates.Count131072.C064526
import PlattCertificates.Count131072.C064527
import PlattCertificates.Count131072.C064528
import PlattCertificates.Count131072.C064529
import PlattCertificates.Count131072.C064530
import PlattCertificates.Count131072.C064531
import PlattCertificates.Count131072.C064532
import PlattCertificates.Count131072.C064533
import PlattCertificates.Count131072.C064534
import PlattCertificates.Count131072.C064535
import PlattCertificates.Count131072.C064536
import PlattCertificates.Count131072.C064537
import PlattCertificates.Count131072.C064538
import PlattCertificates.Count131072.C064539
import PlattCertificates.Count131072.C064540
import PlattCertificates.Count131072.C064541
import PlattCertificates.Count131072.C064542
import PlattCertificates.Count131072.C064543
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000141
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts64512 : List PrefixCut := [⟨64,190251515,190251626⟩]
theorem checked64512 : checkPrefixCuts (2^48) 8459649025 10 Manual.Count131072.C064512.packed 64 cuts64512 = true := by
 decide +kernel
def cuts64513 : List PrefixCut := [⟨18,52436762,52436792⟩,
⟨64,188618243,188618350⟩]
theorem checked64513 : checkPrefixCuts (2^48) 8459780097 10 Manual.Count131072.C064513.packed 64 cuts64513 = true := by
 decide +kernel
def pointBounds64513 : List (Nat × Nat × Nat) := [(8459816960,114810903015432,114811291935953)]
theorem point_links_checked64513 : (cuts64513.take 1).map (fun c => (8459780097-1+2*2^10*c.k,114810850578670+c.lower,114811239499161+c.upper)) = pointBounds64513 := by
 decide +kernel
def cuts64514 : List PrefixCut := [⟨64,193972006,193972118⟩]
theorem checked64514 : checkPrefixCuts (2^48) 8459911169 10 Manual.Count131072.C064514.packed 64 cuts64514 = true := by
 decide +kernel
def cuts64515 : List PrefixCut := [⟨20,58756614,58756652⟩,
⟨64,188179875,188179986⟩]
theorem checked64515 : checkPrefixCuts (2^48) 8460042241 10 Manual.Count131072.C064515.packed 64 cuts64515 = true := by
 decide +kernel
def pointBounds64515 : List (Nat × Nat × Nat) := [(8460083200,114811291925533,114811680846281)]
theorem point_links_checked64515 : (cuts64515.take 1).map (fun c => (8460042241-1+2*2^10*c.k,114811233168919+c.lower,114811622089629+c.upper)) = pointBounds64515 := by
 decide +kernel
def cuts64516 : List PrefixCut := [⟨64,190539158,190539271⟩]
theorem checked64516 : checkPrefixCuts (2^48) 8460173313 10 Manual.Count131072.C064516.packed 64 cuts64516 = true := by
 decide +kernel
def cuts64517 : List PrefixCut := [⟨22,66173985,66174023⟩,
⟨64,192565661,192565771⟩]
theorem checked64517 : checkPrefixCuts (2^48) 8460304385 10 Manual.Count131072.C064517.packed 64 cuts64517 = true := by
 decide +kernel
def pointBounds64517 : List (Nat × Nat × Nat) := [(8460349440,114811678061937,114812066982909)]
theorem point_links_checked64517 : (cuts64517.take 1).map (fun c => (8460304385-1+2*2^10*c.k,114811611887952+c.lower,114812000808886+c.upper)) = pointBounds64517 := by
 decide +kernel
def cuts64518 : List PrefixCut := [⟨64,190599793,190599904⟩]
theorem checked64518 : checkPrefixCuts (2^48) 8460435457 10 Manual.Count131072.C064518.packed 64 cuts64518 = true := by
 decide +kernel
def cuts64519 : List PrefixCut := [⟨24,71195533,71195573⟩,
⟨64,190330678,190330790⟩]
theorem checked64519 : checkPrefixCuts (2^48) 8460566529 10 Manual.Count131072.C064519.packed 64 cuts64519 = true := by
 decide +kernel
def pointBounds64519 : List (Nat × Nat × Nat) := [(8460615680,114812066248939,114812455170134)]
theorem point_links_checked64519 : (cuts64519.take 1).map (fun c => (8460566529-1+2*2^10*c.k,114811995053406+c.lower,114812383974561+c.upper)) = pointBounds64519 := by
 decide +kernel
def cuts64520 : List PrefixCut := [⟨64,190959827,190959936⟩]
theorem checked64520 : checkPrefixCuts (2^48) 8460697601 10 Manual.Count131072.C064520.packed 64 cuts64520 = true := by
 decide +kernel
def cuts64521 : List PrefixCut := [⟨26,78445706,78445753⟩,
⟨64,191422619,191422729⟩]
theorem checked64521 : checkPrefixCuts (2^48) 8460828673 10 Manual.Count131072.C064521.packed 64 cuts64521 = true := by
 decide +kernel
def pointBounds64521 : List (Nat × Nat × Nat) := [(8460881920,114812454789617,114812843711040)]
theorem point_links_checked64521 : (cuts64521.take 1).map (fun c => (8460828673-1+2*2^10*c.k,114812376343911+c.lower,114812765265287+c.upper)) = pointBounds64521 := by
 decide +kernel
def cuts64522 : List PrefixCut := [⟨64,192816869,192816987⟩]
theorem checked64522 : checkPrefixCuts (2^48) 8460959745 10 Manual.Count131072.C064522.packed 64 cuts64522 = true := by
 decide +kernel
def cuts64523 : List PrefixCut := [⟨28,82634885,82634935⟩,
⟨64,190984217,190984331⟩]
theorem checked64523 : checkPrefixCuts (2^48) 8461090817 10 Manual.Count131072.C064523.packed 64 cuts64523 = true := by
 decide +kernel
def pointBounds64523 : List (Nat × Nat × Nat) := [(8461148160,114812843218284,114813232139938)]
theorem point_links_checked64523 : (cuts64523.take 1).map (fun c => (8461090817-1+2*2^10*c.k,114812760583399+c.lower,114813149505003+c.upper)) = pointBounds64523 := by
 decide +kernel
def cuts64524 : List PrefixCut := [⟨64,189650621,189650733⟩]
theorem checked64524 : checkPrefixCuts (2^48) 8461221889 10 Manual.Count131072.C064524.packed 64 cuts64524 = true := by
 decide +kernel
def cuts64525 : List PrefixCut := [⟨30,92811649,92811699⟩,
⟨64,193938962,193939073⟩]
theorem checked64525 : checkPrefixCuts (2^48) 8461352961 10 Manual.Count131072.C064525.packed 64 cuts64525 = true := by
 decide +kernel
def pointBounds64525 : List (Nat × Nat × Nat) := [(8461414400,114813234029886,114813622951766)]
theorem point_links_checked64525 : (cuts64525.take 1).map (fun c => (8461352961-1+2*2^10*c.k,114813141218237+c.lower,114813530140067+c.upper)) = pointBounds64525 := by
 decide +kernel
def cuts64526 : List PrefixCut := [⟨64,191308005,191308108⟩]
theorem checked64526 : checkPrefixCuts (2^48) 8461484033 10 Manual.Count131072.C064526.packed 64 cuts64526 = true := by
 decide +kernel
def cuts64527 : List PrefixCut := [⟨32,95237078,95237130⟩,
⟨64,188776927,188777034⟩]
theorem checked64527 : checkPrefixCuts (2^48) 8461615105 10 Manual.Count131072.C064527.packed 64 cuts64527 = true := by
 decide +kernel
def pointBounds64527 : List (Nat × Nat × Nat) := [(8461680640,114813621702282,114814010624378)]
theorem point_links_checked64527 : (cuts64527.take 1).map (fun c => (8461615105-1+2*2^10*c.k,114813526465204+c.lower,114813915387248+c.upper)) = pointBounds64527 := by
 decide +kernel
def cuts64528 : List PrefixCut := [⟨64,190869630,190869741⟩]
theorem checked64528 : checkPrefixCuts (2^48) 8461746177 10 Manual.Count131072.C064528.packed 64 cuts64528 = true := by
 decide +kernel
def cuts64529 : List PrefixCut := [⟨34,101753804,101753864⟩,
⟨64,190068363,190068479⟩]
theorem checked64529 : checkPrefixCuts (2^48) 8461877249 10 Manual.Count131072.C064529.packed 64 cuts64529 = true := by
 decide +kernel
def pointBounds64529 : List (Nat × Nat × Nat) := [(8461946880,114814007865565,114814396787887)]
theorem point_links_checked64529 : (cuts64529.take 1).map (fun c => (8461877249-1+2*2^10*c.k,114813906111761+c.lower,114814295034023+c.upper)) = pointBounds64529 := by
 decide +kernel
def cuts64530 : List PrefixCut := [⟨64,191528981,191529089⟩]
theorem checked64530 : checkPrefixCuts (2^48) 8462008321 10 Manual.Count131072.C064530.packed 64 cuts64530 = true := by
 decide +kernel
def cuts64531 : List PrefixCut := [⟨36,106141296,106141362⟩,
⟨64,190694441,190694558⟩]
theorem checked64531 : checkPrefixCuts (2^48) 8462139393 10 Manual.Count131072.C064531.packed 64 cuts64531 = true := by
 decide +kernel
def pointBounds64531 : List (Nat × Nat × Nat) := [(8462213120,114814393850401,114814782772953)]
theorem point_links_checked64531 : (cuts64531.take 1).map (fun c => (8462139393-1+2*2^10*c.k,114814287709105+c.lower,114814676631591+c.upper)) = pointBounds64531 := by
 decide +kernel
def cuts64532 : List PrefixCut := [⟨64,191855675,191855789⟩]
theorem checked64532 : checkPrefixCuts (2^48) 8462270465 10 Manual.Count131072.C064532.packed 64 cuts64532 = true := by
 decide +kernel
def cuts64533 : List PrefixCut := [⟨38,114752754,114752824⟩,
⟨64,192551198,192551312⟩]
theorem checked64533 : checkPrefixCuts (2^48) 8462401537 10 Manual.Count131072.C064533.packed 64 cuts64533 = true := by
 decide +kernel
def pointBounds64533 : List (Nat × Nat × Nat) := [(8462479360,114814785011975,114815173934762)]
theorem point_links_checked64533 : (cuts64533.take 1).map (fun c => (8462401537-1+2*2^10*c.k,114814670259221+c.lower,114815059181938+c.upper)) = pointBounds64533 := by
 decide +kernel
def cuts64534 : List PrefixCut := [⟨64,190918443,190918552⟩]
theorem checked64534 : checkPrefixCuts (2^48) 8462532609 10 Manual.Count131072.C064534.packed 64 cuts64534 = true := by
 decide +kernel
def cuts64535 : List PrefixCut := [⟨40,116345686,116345753⟩,
⟨64,189152646,189152754⟩]
theorem checked64535 : checkPrefixCuts (2^48) 8462663681 10 Manual.Count131072.C064535.packed 64 cuts64535 = true := by
 decide +kernel
def pointBounds64535 : List (Nat × Nat × Nat) := [(8462745600,114815170074548,114815558997555)]
theorem point_links_checked64535 : (cuts64535.take 1).map (fun c => (8462663681-1+2*2^10*c.k,114815053728862+c.lower,114815442651802+c.upper)) = pointBounds64535 := by
 decide +kernel
def cuts64536 : List PrefixCut := [⟨64,191178593,191178707⟩]
theorem checked64536 : checkPrefixCuts (2^48) 8462794753 10 Manual.Count131072.C064536.packed 64 cuts64536 = true := by
 decide +kernel
def cuts64537 : List PrefixCut := [⟨42,127417505,127417582⟩,
⟨64,191874092,191874211⟩]
theorem checked64537 : checkPrefixCuts (2^48) 8462925825 10 Manual.Count131072.C064537.packed 64 cuts64537 = true := by
 decide +kernel
def pointBounds64537 : List (Nat × Nat × Nat) := [(8463011840,114815561477606,114815950400845)]
theorem point_links_checked64537 : (cuts64537.take 1).map (fun c => (8462925825-1+2*2^10*c.k,114815434060101+c.lower,114815822983263+c.upper)) = pointBounds64537 := by
 decide +kernel
def cuts64538 : List PrefixCut := [⟨64,191305712,191305820⟩]
theorem checked64538 : checkPrefixCuts (2^48) 8463056897 10 Manual.Count131072.C064538.packed 64 cuts64538 = true := by
 decide +kernel
def cuts64539 : List PrefixCut := [⟨44,131770390,131770464⟩,
⟨64,191435775,191435882⟩]
theorem checked64539 : checkPrefixCuts (2^48) 8463187969 10 Manual.Count131072.C064539.packed 64 cuts64539 = true := by
 decide +kernel
def pointBounds64539 : List (Nat × Nat × Nat) := [(8463278080,114815949010295,114816337933758)]
theorem point_links_checked64539 : (cuts64539.take 1).map (fun c => (8463187969-1+2*2^10*c.k,114815817239905+c.lower,114816206163294+c.upper)) = pointBounds64539 := by
 decide +kernel
def cuts64540 : List PrefixCut := [⟨64,189404085,189404199⟩]
theorem checked64540 : checkPrefixCuts (2^48) 8463319041 10 Manual.Count131072.C064540.packed 64 cuts64540 = true := by
 decide +kernel
def cuts64541 : List PrefixCut := [⟨46,136355811,136355887⟩,
⟨64,190299081,190299189⟩]
theorem checked64541 : checkPrefixCuts (2^48) 8463450113 10 Manual.Count131072.C064541.packed 64 cuts64541 = true := by
 decide +kernel
def pointBounds64541 : List (Nat × Nat × Nat) := [(8463544320,114816334435576,114816723359262)]
theorem point_links_checked64541 : (cuts64541.take 1).map (fun c => (8463450113-1+2*2^10*c.k,114816198079765+c.lower,114816587003375+c.upper)) = pointBounds64541 := by
 decide +kernel
def cuts64542 : List PrefixCut := [⟨64,191759442,191759551⟩]
theorem checked64542 : checkPrefixCuts (2^48) 8463581185 10 Manual.Count131072.C064542.packed 64 cuts64542 = true := by
 decide +kernel
def cuts64543 : List PrefixCut := [⟨48,143801012,143801095⟩,
⟨64,190758794,190758904⟩]
theorem checked64543 : checkPrefixCuts (2^48) 8463712257 10 Manual.Count131072.C064543.packed 64 cuts64543 = true := by
 decide +kernel
def pointBounds64543 : List (Nat × Nat × Nat) := [(8463810560,114816723939300,114817112863210)]
theorem point_links_checked64543 : (cuts64543.take 1).map (fun c => (8463712257-1+2*2^10*c.k,114816580138288+c.lower,114816969062115+c.upper)) = pointBounds64543 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000141
