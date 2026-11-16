import PlattAssemblyKernel
import PlattCertificates.Count131072.C052496
import PlattCertificates.Count131072.C052497
import PlattCertificates.Count131072.C052498
import PlattCertificates.Count131072.C052499
import PlattCertificates.Count131072.C052500
import PlattCertificates.Count131072.C052501
import PlattCertificates.Count131072.C052502
import PlattCertificates.Count131072.C052503
import PlattCertificates.Count131072.C052504
import PlattCertificates.Count131072.C052505
import PlattCertificates.Count131072.C052506
import PlattCertificates.Count131072.C052507
import PlattCertificates.Count131072.C052508
import PlattCertificates.Count131072.C052509
import PlattCertificates.Count131072.C052510
import PlattCertificates.Count131072.C052511
import PlattCertificates.Count131072.C052512
import PlattCertificates.Count131072.C052513
import PlattCertificates.Count131072.C052514
import PlattCertificates.Count131072.C052515
import PlattCertificates.Count131072.C052516
import PlattCertificates.Count131072.C052517
import PlattCertificates.Count131072.C052518
import PlattCertificates.Count131072.C052519
import PlattCertificates.Count131072.C052520
import PlattCertificates.Count131072.C052521
import PlattCertificates.Count131072.C052522
import PlattCertificates.Count131072.C052523
import PlattCertificates.Count131072.C052524
import PlattCertificates.Count131072.C052525
import PlattCertificates.Count131072.C052526
import PlattCertificates.Count131072.C052527
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000078
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts52496 : List PrefixCut := [⟨64,240274112,240274249⟩]
theorem checked52496 : checkPrefixCuts (2^48) 6884687873 10 Manual.Count131072.C052496.packed 64 cuts52496 = true := by
 decide +kernel
def cuts52497 : List PrefixCut := [⟨12,43377224,43377248⟩,
⟨64,234832073,234832211⟩]
theorem checked52497 : checkPrefixCuts (2^48) 6884818945 10 Manual.Count131072.C052497.packed 64 cuts52497 = true := by
 decide +kernel
def pointBounds52497 : List (Nat × Nat × Nat) := [(6884843520,112262723492342,112263110958894)]
theorem point_links_checked52497 : (cuts52497.take 1).map (fun c => (6884818945-1+2*2^10*c.k,112262680115118+c.lower,112263067581646+c.upper)) = pointBounds52497 := by
 decide +kernel
def cuts52498 : List PrefixCut := [⟨54,200813895,200814009⟩,
⟨64,238711433,238711569⟩]
theorem checked52498 : checkPrefixCuts (2^48) 6884950017 10 Manual.Count131072.C052498.packed 64 cuts52498 = true := by
 decide +kernel
def pointBounds52498 : List (Nat × Nat × Nat) := [(6885060608,112263115761086,112263503227866)]
theorem point_links_checked52498 : (cuts52498.take 1).map (fun c => (6884950017-1+2*2^10*c.k,112262914947191+c.lower,112263302413857+c.upper)) = pointBounds52498 := by
 decide +kernel
def cuts52499 : List PrefixCut := [⟨64,233310526,233310655⟩]
theorem checked52499 : checkPrefixCuts (2^48) 6885081089 10 Manual.Count131072.C052499.packed 64 cuts52499 = true := by
 decide +kernel
def cuts52500 : List PrefixCut := [⟨32,117287262,117287329⟩,
⟨64,236331269,236331402⟩]
theorem checked52500 : checkPrefixCuts (2^48) 6885212161 10 Manual.Count131072.C052500.packed 64 cuts52500 = true := by
 decide +kernel
def pointBounds52500 : List (Nat × Nat × Nat) := [(6885277696,112263504256412,112263891723410)]
theorem point_links_checked52500 : (cuts52500.take 1).map (fun c => (6885212161-1+2*2^10*c.k,112263386969150+c.lower,112263774436081+c.upper)) = pointBounds52500 := by
 decide +kernel
def cuts52501 : List PrefixCut := [⟨64,235754470,235754605⟩]
theorem checked52501 : checkPrefixCuts (2^48) 6885343233 10 Manual.Count131072.C052501.packed 64 cuts52501 = true := by
 decide +kernel
def cuts52502 : List PrefixCut := [⟨10,36995911,36995931⟩,
⟨64,235831716,235831852⟩]
theorem checked52502 : checkPrefixCuts (2^48) 6885474305 10 Manual.Count131072.C052502.packed 64 cuts52502 = true := by
 decide +kernel
def pointBounds52502 : List (Nat × Nat × Nat) := [(6885494784,112263896050800,112264283518019)]
theorem point_links_checked52502 : (cuts52502.take 1).map (fun c => (6885474305-1+2*2^10*c.k,112263859054889+c.lower,112264246522088+c.upper)) = pointBounds52502 := by
 decide +kernel
def cuts52503 : List PrefixCut := [⟨52,191433691,191433800⟩,
⟨64,233783338,233783472⟩]
theorem checked52503 : checkPrefixCuts (2^48) 6885605377 10 Manual.Count131072.C052503.packed 64 cuts52503 = true := by
 decide +kernel
def pointBounds52503 : List (Nat × Nat × Nat) := [(6885711872,112264286320296,112264673787740)]
theorem point_links_checked52503 : (cuts52503.take 1).map (fun c => (6885605377-1+2*2^10*c.k,112264094886605+c.lower,112264482353940+c.upper)) = pointBounds52503 := by
 decide +kernel
def cuts52504 : List PrefixCut := [⟨64,237498721,237498854⟩]
theorem checked52504 : checkPrefixCuts (2^48) 6885736449 10 Manual.Count131072.C052504.packed 64 cuts52504 = true := by
 decide +kernel
def cuts52505 : List PrefixCut := [⟨30,110204407,110204473⟩,
⟨64,236676663,236676800⟩]
theorem checked52505 : checkPrefixCuts (2^48) 6885867521 10 Manual.Count131072.C052505.packed 64 cuts52505 = true := by
 decide +kernel
def pointBounds52505 : List (Nat × Nat × Nat) := [(6885928960,112264676373071,112265063840739)]
theorem point_links_checked52505 : (cuts52505.take 1).map (fun c => (6885867521-1+2*2^10*c.k,112264566168664+c.lower,112264953636266+c.upper)) = pointBounds52505 := by
 decide +kernel
def cuts52506 : List PrefixCut := [⟨64,234137856,234137993⟩]
theorem checked52506 : checkPrefixCuts (2^48) 6885998593 10 Manual.Count131072.C052506.packed 64 cuts52506 = true := by
 decide +kernel
def cuts52507 : List PrefixCut := [⟨8,30738440,30738456⟩,
⟨64,239406311,239406440⟩]
theorem checked52507 : checkPrefixCuts (2^48) 6886129665 10 Manual.Count131072.C052507.packed 64 cuts52507 = true := by
 decide +kernel
def pointBounds52507 : List (Nat × Nat × Nat) := [(6886146048,112265067721623,112265455189515)]
theorem point_links_checked52507 : (cuts52507.take 1).map (fun c => (6886129665-1+2*2^10*c.k,112265036983183+c.lower,112265424451059+c.upper)) = pointBounds52507 := by
 decide +kernel
def cuts52508 : List PrefixCut := [⟨50,186551434,186551542⟩,
⟨64,239074728,239074865⟩]
theorem checked52508 : checkPrefixCuts (2^48) 6886260737 10 Manual.Count131072.C052508.packed 64 cuts52508 = true := by
 decide +kernel
def pointBounds52508 : List (Nat × Nat × Nat) := [(6886363136,112265462940928,112265850409041)]
theorem point_links_checked52508 : (cuts52508.take 1).map (fun c => (6886260737-1+2*2^10*c.k,112265276389494+c.lower,112265663857499+c.upper)) = pointBounds52508 := by
 decide +kernel
def cuts52509 : List PrefixCut := [⟨64,233061748,233061881⟩]
theorem checked52509 : checkPrefixCuts (2^48) 6886391809 10 Manual.Count131072.C052509.packed 64 cuts52509 = true := by
 decide +kernel
def cuts52510 : List PrefixCut := [⟨28,101896706,101896763⟩,
⟨64,235959290,235959425⟩]
theorem checked52510 : checkPrefixCuts (2^48) 6886522881 10 Manual.Count131072.C052510.packed 64 cuts52510 = true := by
 decide +kernel
def pointBounds52510 : List (Nat × Nat × Nat) := [(6886580224,112265850422676,112266237891008)]
theorem point_links_checked52510 : (cuts52510.take 1).map (fun c => (6886522881-1+2*2^10*c.k,112265748525970+c.lower,112266135994245+c.upper)) = pointBounds52510 := by
 decide +kernel
def cuts52511 : List PrefixCut := [⟨64,237467099,237467230⟩]
theorem checked52511 : checkPrefixCuts (2^48) 6886653953 10 Manual.Count131072.C052511.packed 64 cuts52511 = true := by
 decide +kernel
def cuts52512 : List PrefixCut := [⟨6,21825490,21825503⟩,
⟨64,233743258,233743392⟩]
theorem checked52512 : checkPrefixCuts (2^48) 6886785025 10 Manual.Count131072.C052512.packed 64 cuts52512 = true := by
 decide +kernel
def pointBounds52512 : List (Nat × Nat × Nat) := [(6886797312,112266243777849,112266631246403)]
theorem point_links_checked52512 : (cuts52512.take 1).map (fun c => (6886785025-1+2*2^10*c.k,112266221952359+c.lower,112266609420900+c.upper)) = pointBounds52512 := by
 decide +kernel
def cuts52513 : List PrefixCut := [⟨48,180484880,180484981⟩,
⟨64,240564195,240564332⟩]
theorem checked52513 : checkPrefixCuts (2^48) 6886916097 10 Manual.Count131072.C052513.packed 64 cuts52513 = true := by
 decide +kernel
def pointBounds52513 : List (Nat × Nat × Nat) := [(6887014400,112266636180497,112267023649273)]
theorem point_links_checked52513 : (cuts52513.take 1).map (fun c => (6886916097-1+2*2^10*c.k,112266455695617+c.lower,112266843164292+c.upper)) = pointBounds52513 := by
 decide +kernel
def cuts52514 : List PrefixCut := [⟨64,231404783,231404916⟩]
theorem checked52514 : checkPrefixCuts (2^48) 6887047169 10 Manual.Count131072.C052514.packed 64 cuts52514 = true := by
 decide +kernel
def cuts52515 : List PrefixCut := [⟨26,95593178,95593233⟩,
⟨64,234547305,234547442⟩]
theorem checked52515 : checkPrefixCuts (2^48) 6887178241 10 Manual.Count131072.C052515.packed 64 cuts52515 = true := by
 decide +kernel
def pointBounds52515 : List (Nat × Nat × Nat) := [(6887231488,112267023257773,112267410726773)]
theorem point_links_checked52515 : (cuts52515.take 1).map (fun c => (6887178241-1+2*2^10*c.k,112266927664595+c.lower,112267315133540+c.upper)) = pointBounds52515 := by
 decide +kernel
def cuts52516 : List PrefixCut := [⟨64,234379361,234379494⟩]
theorem checked52516 : checkPrefixCuts (2^48) 6887309313 10 Manual.Count131072.C052516.packed 64 cuts52516 = true := by
 decide +kernel
def cuts52517 : List PrefixCut := [⟨4,15161964,15161972⟩,
⟨64,235192246,235192378⟩]
theorem checked52517 : checkPrefixCuts (2^48) 6887440385 10 Manual.Count131072.C052517.packed 64 cuts52517 = true := by
 decide +kernel
def pointBounds52517 : List (Nat × Nat × Nat) := [(6887448576,112267411753225,112267799222448)]
theorem point_links_checked52517 : (cuts52517.take 1).map (fun c => (6887440385-1+2*2^10*c.k,112267396591261+c.lower,112267784060476+c.upper)) = pointBounds52517 := by
 decide +kernel
def cuts52518 : List PrefixCut := [⟨46,174378621,174378721⟩,
⟨64,241522125,241522264⟩]
theorem checked52518 : checkPrefixCuts (2^48) 6887571457 10 Manual.Count131072.C052518.packed 64 cuts52518 = true := by
 decide +kernel
def pointBounds52518 : List (Nat × Nat × Nat) := [(6887665664,112267806162128,112268193631575)]
theorem point_links_checked52518 : (cuts52518.take 1).map (fun c => (6887571457-1+2*2^10*c.k,112267631783507+c.lower,112268019252854+c.upper)) = pointBounds52518 := by
 decide +kernel
def cuts52519 : List PrefixCut := [⟨64,236491014,236491152⟩]
theorem checked52519 : checkPrefixCuts (2^48) 6887702529 10 Manual.Count131072.C052519.packed 64 cuts52519 = true := by
 decide +kernel
def cuts52520 : List PrefixCut := [⟨24,88432673,88432721⟩,
⟨64,234525000,234525130⟩]
theorem checked52520 : checkPrefixCuts (2^48) 6887833601 10 Manual.Count131072.C052520.packed 64 cuts52520 = true := by
 decide +kernel
def pointBounds52520 : List (Nat × Nat × Nat) := [(6887882752,112268198229319,112268585698991)]
theorem point_links_checked52520 : (cuts52520.take 1).map (fun c => (6887833601-1+2*2^10*c.k,112268109796646+c.lower,112268497266270+c.upper)) = pointBounds52520 := by
 decide +kernel
def cuts52521 : List PrefixCut := [⟨64,239465101,239465238⟩]
theorem checked52521 : checkPrefixCuts (2^48) 6887964673 10 Manual.Count131072.C052521.packed 64 cuts52521 = true := by
 decide +kernel
def cuts52522 : List PrefixCut := [⟨2,7355511,7355515⟩,
⟨64,236763555,236763690⟩]
theorem checked52522 : checkPrefixCuts (2^48) 6888095745 10 Manual.Count131072.C052522.packed 64 cuts52522 = true := by
 decide +kernel
def pointBounds52522 : List (Nat × Nat × Nat) := [(6888099840,112268591142258,112268978612153)]
theorem point_links_checked52522 : (cuts52522.take 1).map (fun c => (6888095745-1+2*2^10*c.k,112268583786747+c.lower,112268971256638+c.upper)) = pointBounds52522 := by
 decide +kernel
def cuts52523 : List PrefixCut := [⟨44,161694561,161694654⟩,
⟨64,235982642,235982777⟩]
theorem checked52523 : checkPrefixCuts (2^48) 6888226817 10 Manual.Count131072.C052523.packed 64 cuts52523 = true := by
 decide +kernel
def pointBounds52523 : List (Nat × Nat × Nat) := [(6888316928,112268982244863,112269369714982)]
theorem point_links_checked52523 : (cuts52523.take 1).map (fun c => (6888226817-1+2*2^10*c.k,112268820550302+c.lower,112269208020328+c.upper)) = pointBounds52523 := by
 decide +kernel
def cuts52524 : List PrefixCut := [⟨64,237367469,237367606⟩]
theorem checked52524 : checkPrefixCuts (2^48) 6888357889 10 Manual.Count131072.C052524.packed 64 cuts52524 = true := by
 decide +kernel
def cuts52525 : List PrefixCut := [⟨22,79965948,79965995⟩,
⟨64,232990794,232990928⟩]
theorem checked52525 : checkPrefixCuts (2^48) 6888488961 10 Manual.Count131072.C052525.packed 64 cuts52525 = true := by
 decide +kernel
def pointBounds52525 : List (Nat × Nat × Nat) := [(6888534016,112269373866361,112269761336706)]
theorem point_links_checked52525 : (cuts52525.take 1).map (fun c => (6888488961-1+2*2^10*c.k,112269293900413+c.lower,112269681370711+c.upper)) = pointBounds52525 := by
 decide +kernel
def cuts52526 : List PrefixCut := [⟨64,230330448,230330587⟩]
theorem checked52526 : checkPrefixCuts (2^48) 6888620033 10 Manual.Count131072.C052526.packed 64 cuts52526 = true := by
 decide +kernel
def pointBounds52526 : List (Nat × Nat × Nat) := [(6888751104,112269757221655,112270144692226)]
theorem point_links_checked52526 : (cuts52526.take 1).map (fun c => (6888620033-1+2*2^10*c.k,112269526891207+c.lower,112269914361639+c.upper)) = pointBounds52526 := by
 decide +kernel
def cuts52527 : List PrefixCut := [⟨64,237803387,237803523⟩]
theorem checked52527 : checkPrefixCuts (2^48) 6888751105 10 Manual.Count131072.C052527.packed 64 cuts52527 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000078
