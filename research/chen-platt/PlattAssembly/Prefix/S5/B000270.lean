import PlattAssemblyKernel
import PlattCertificates.Count131072.C048640
import PlattCertificates.Count131072.C048641
import PlattCertificates.Count131072.C048642
import PlattCertificates.Count131072.C048643
import PlattCertificates.Count131072.C048644
import PlattCertificates.Count131072.C048645
import PlattCertificates.Count131072.C048646
import PlattCertificates.Count131072.C048647
import PlattCertificates.Count131072.C048648
import PlattCertificates.Count131072.C048649
import PlattCertificates.Count131072.C048650
import PlattCertificates.Count131072.C048651
import PlattCertificates.Count131072.C048652
import PlattCertificates.Count131072.C048653
import PlattCertificates.Count131072.C048654
import PlattCertificates.Count131072.C048655
import PlattCertificates.Count131072.C048656
import PlattCertificates.Count131072.C048657
import PlattCertificates.Count131072.C048658
import PlattCertificates.Count131072.C048659
import PlattCertificates.Count131072.C048660
import PlattCertificates.Count131072.C048661
import PlattCertificates.Count131072.C048662
import PlattCertificates.Count131072.C048663
import PlattCertificates.Count131072.C048664
import PlattCertificates.Count131072.C048665
import PlattCertificates.Count131072.C048666
import PlattCertificates.Count131072.C048667
import PlattCertificates.Count131072.C048668
import PlattCertificates.Count131072.C048669
import PlattCertificates.Count131072.C048670
import PlattCertificates.Count131072.C048671
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000270
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts48640 : List PrefixCut := [⟨64,257545308,257545457⟩]
theorem checked48640 : checkPrefixCuts (2^48) 6379274241 10 Manual.Count131072.C048640.packed 64 cuts48640 = true := by
 decide +kernel
def cuts48641 : List PrefixCut := [⟨24,96627755,96627810⟩,
⟨64,256172231,256172371⟩]
theorem checked48641 : checkPrefixCuts (2^48) 6379405313 10 Manual.Count131072.C048641.packed 64 cuts48641 = true := by
 decide +kernel
def pointBounds48641 : List (Nat × Nat × Nat) := [(6379454464,111313828904060,111314215830450)]
theorem point_links_checked48641 : (cuts48641.take 1).map (fun c => (6379405313-1+2*2^10*c.k,111313732276305+c.lower,111314119202640+c.upper)) = pointBounds48641 := by
 decide +kernel
def cuts48642 : List PrefixCut := [⟨58,234459616,234459750⟩,
⟨64,258637741,258637887⟩]
theorem checked48642 : checkPrefixCuts (2^48) 6379536385 10 Manual.Count131072.C048642.packed 64 cuts48642 = true := by
 decide +kernel
def pointBounds48642 : List (Nat × Nat × Nat) := [(6379655168,111314222908152,111314609834761)]
theorem point_links_checked48642 : (cuts48642.take 1).map (fun c => (6379536385-1+2*2^10*c.k,111313988448536+c.lower,111314375375011+c.upper)) = pointBounds48642 := by
 decide +kernel
def cuts48643 : List PrefixCut := [⟨64,254176291,254176436⟩]
theorem checked48643 : checkPrefixCuts (2^48) 6379667457 10 Manual.Count131072.C048643.packed 64 cuts48643 = true := by
 decide +kernel
def cuts48644 : List PrefixCut := [⟨28,112548882,112548949⟩,
⟨64,256994701,256994857⟩]
theorem checked48644 : checkPrefixCuts (2^48) 6379798529 10 Manual.Count131072.C048644.packed 64 cuts48644 = true := by
 decide +kernel
def pointBounds48644 : List (Nat × Nat × Nat) := [(6379855872,111314613811450,111315000738283)]
theorem point_links_checked48644 : (cuts48644.take 1).map (fun c => (6379798529-1+2*2^10*c.k,111314501262568+c.lower,111314888189334+c.upper)) = pointBounds48644 := by
 decide +kernel
def cuts48645 : List PrefixCut := [⟨62,245342250,245342392⟩,
⟨64,253459947,253460093⟩]
theorem checked48645 : checkPrefixCuts (2^48) 6379929601 10 Manual.Count131072.C048645.packed 64 cuts48645 = true := by
 decide +kernel
def pointBounds48645 : List (Nat × Nat × Nat) := [(6380056576,111315003599519,111315390526583)]
theorem point_links_checked48645 : (cuts48645.take 1).map (fun c => (6379929601-1+2*2^10*c.k,111314758257269+c.lower,111315145184191+c.upper)) = pointBounds48645 := by
 decide +kernel
def cuts48646 : List PrefixCut := [⟨64,259984123,259984272⟩]
theorem checked48646 : checkPrefixCuts (2^48) 6380060673 10 Manual.Count131072.C048646.packed 64 cuts48646 = true := by
 decide +kernel
def cuts48647 : List PrefixCut := [⟨32,129526834,129526907⟩,
⟨64,260022899,260023044⟩]
theorem checked48647 : checkPrefixCuts (2^48) 6380191745 10 Manual.Count131072.C048647.packed 64 cuts48647 = true := by
 decide +kernel
def pointBounds48647 : List (Nat × Nat × Nat) := [(6380257280,111315401228173,111315788155463)]
theorem point_links_checked48647 : (cuts48647.take 1).map (fun c => (6380191745-1+2*2^10*c.k,111315271701339+c.lower,111315658628556+c.upper)) = pointBounds48647 := by
 decide +kernel
def cuts48648 : List PrefixCut := [⟨64,254150210,254150352⟩]
theorem checked48648 : checkPrefixCuts (2^48) 6380322817 10 Manual.Count131072.C048648.packed 64 cuts48648 = true := by
 decide +kernel
def cuts48649 : List PrefixCut := [⟨2,8558343,8558348⟩,
⟨64,254806690,254806834⟩]
theorem checked48649 : checkPrefixCuts (2^48) 6380453889 10 Manual.Count131072.C048649.packed 64 cuts48649 = true := by
 decide +kernel
def pointBounds48649 : List (Nat × Nat × Nat) := [(6380457984,111315794432791,111316181360300)]
theorem point_links_checked48649 : (cuts48649.take 1).map (fun c => (6380453889-1+2*2^10*c.k,111315785874448+c.lower,111316172801952+c.upper)) = pointBounds48649 := by
 decide +kernel
def cuts48650 : List PrefixCut := [⟨36,145135134,145135216⟩,
⟨64,257801199,257801342⟩]
theorem checked48650 : checkPrefixCuts (2^48) 6380584961 10 Manual.Count131072.C048650.packed 64 cuts48650 = true := by
 decide +kernel
def pointBounds48650 : List (Nat × Nat × Nat) := [(6380658688,111316185816272,111316572744002)]
theorem point_links_checked48650 : (cuts48650.take 1).map (fun c => (6380584961-1+2*2^10*c.k,111316040681138+c.lower,111316427608786+c.upper)) = pointBounds48650 := by
 decide +kernel
def cuts48651 : List PrefixCut := [⟨64,260266216,260266364⟩]
theorem checked48651 : checkPrefixCuts (2^48) 6380716033 10 Manual.Count131072.C048651.packed 64 cuts48651 = true := by
 decide +kernel
def cuts48652 : List PrefixCut := [⟨6,23467806,23467821⟩,
⟨64,258408146,258408294⟩]
theorem checked48652 : checkPrefixCuts (2^48) 6380847105 10 Manual.Count131072.C048652.packed 64 cuts48652 = true := by
 decide +kernel
def pointBounds48652 : List (Nat × Nat × Nat) := [(6380859392,111316582216359,111316969144313)]
theorem point_links_checked48652 : (cuts48652.take 1).map (fun c => (6380847105-1+2*2^10*c.k,111316558748553+c.lower,111316945676492+c.upper)) = pointBounds48652 := by
 decide +kernel
def cuts48653 : List PrefixCut := [⟨40,161006148,161006245⟩,
⟨64,256947188,256947338⟩]
theorem checked48653 : checkPrefixCuts (2^48) 6380978177 10 Manual.Count131072.C048653.packed 64 cuts48653 = true := by
 decide +kernel
def pointBounds48653 : List (Nat × Nat × Nat) := [(6381060096,111316978162847,111317365091031)]
theorem point_links_checked48653 : (cuts48653.take 1).map (fun c => (6380978177-1+2*2^10*c.k,111316817156699+c.lower,111317204084786+c.upper)) = pointBounds48653 := by
 decide +kernel
def cuts48654 : List PrefixCut := [⟨64,252354464,252354604⟩]
theorem checked48654 : checkPrefixCuts (2^48) 6381109249 10 Manual.Count131072.C048654.packed 64 cuts48654 = true := by
 decide +kernel
def cuts48655 : List PrefixCut := [⟨10,39566381,39566404⟩,
⟨64,258127575,258127723⟩]
theorem checked48655 : checkPrefixCuts (2^48) 6381240321 10 Manual.Count131072.C048655.packed 64 cuts48655 = true := by
 decide +kernel
def pointBounds48655 : List (Nat × Nat × Nat) := [(6381260800,111317366024732,111317752953132)]
theorem point_links_checked48655 : (cuts48655.take 1).map (fun c => (6381240321-1+2*2^10*c.k,111317326458351+c.lower,111317713386728+c.upper)) = pointBounds48655 := by
 decide +kernel
def cuts48656 : List PrefixCut := [⟨44,176434123,176434224⟩,
⟨64,257019579,257019730⟩]
theorem checked48656 : checkPrefixCuts (2^48) 6381371393 10 Manual.Count131072.C048656.packed 64 cuts48656 = true := by
 decide +kernel
def pointBounds48656 : List (Nat × Nat × Nat) := [(6381461504,111317761020049,111318147948675)]
theorem point_links_checked48656 : (cuts48656.take 1).map (fun c => (6381371393-1+2*2^10*c.k,111317584585926+c.lower,111317971514451+c.upper)) = pointBounds48656 := by
 decide +kernel
def cuts48657 : List PrefixCut := [⟨64,253838565,253838712⟩]
theorem checked48657 : checkPrefixCuts (2^48) 6381502465 10 Manual.Count131072.C048657.packed 64 cuts48657 = true := by
 decide +kernel
def cuts48658 : List PrefixCut := [⟨14,57250794,57250830⟩,
⟨64,254891910,254892063⟩]
theorem checked48658 : checkPrefixCuts (2^48) 6381633537 10 Manual.Count131072.C048658.packed 64 cuts48658 = true := by
 decide +kernel
def pointBounds48658 : List (Nat × Nat × Nat) := [(6381662208,111318152694864,111318539623723)]
theorem point_links_checked48658 : (cuts48658.take 1).map (fun c => (6381633537-1+2*2^10*c.k,111318095444070+c.lower,111318482372893+c.upper)) = pointBounds48658 := by
 decide +kernel
def cuts48659 : List PrefixCut := [⟨48,192521750,192521863⟩,
⟨64,258106378,258106526⟩]
theorem checked48659 : checkPrefixCuts (2^48) 6381764609 10 Manual.Count131072.C048659.packed 64 cuts48659 = true := by
 decide +kernel
def pointBounds48659 : List (Nat × Nat × Nat) := [(6381862912,111318542857730,111318929786819)]
theorem point_links_checked48659 : (cuts48659.take 1).map (fun c => (6381764609-1+2*2^10*c.k,111318350335980+c.lower,111318737264956+c.upper)) = pointBounds48659 := by
 decide +kernel
def cuts48660 : List PrefixCut := [⟨64,258145186,258145329⟩]
theorem checked48660 : checkPrefixCuts (2^48) 6381895681 10 Manual.Count131072.C048660.packed 64 cuts48660 = true := by
 decide +kernel
def cuts48661 : List PrefixCut := [⟨18,71713404,71713444⟩,
⟨64,253994118,253994264⟩]
theorem checked48661 : checkPrefixCuts (2^48) 6382026753 10 Manual.Count131072.C048661.packed 64 cuts48661 = true := by
 decide +kernel
def pointBounds48661 : List (Nat × Nat × Nat) := [(6382063616,111318938300948,111319325230255)]
theorem point_links_checked48661 : (cuts48661.take 1).map (fun c => (6382026753-1+2*2^10*c.k,111318866587544+c.lower,111319253516811+c.upper)) = pointBounds48661 := by
 decide +kernel
def cuts48662 : List PrefixCut := [⟨52,209489430,209489548⟩,
⟨64,258222787,258222933⟩]
theorem checked48662 : checkPrefixCuts (2^48) 6382157825 10 Manual.Count131072.C048662.packed 64 cuts48662 = true := by
 decide +kernel
def pointBounds48662 : List (Nat × Nat × Nat) := [(6382264320,111319330071092,111319717000623)]
theorem point_links_checked48662 : (cuts48662.take 1).map (fun c => (6382157825-1+2*2^10*c.k,111319120581662+c.lower,111319507511075+c.upper)) = pointBounds48662 := by
 decide +kernel
def cuts48663 : List PrefixCut := [⟨64,253322153,253322297⟩]
theorem checked48663 : checkPrefixCuts (2^48) 6382288897 10 Manual.Count131072.C048663.packed 64 cuts48663 = true := by
 decide +kernel
def cuts48664 : List PrefixCut := [⟨22,86041905,86041956⟩,
⟨64,256095305,256095451⟩]
theorem checked48664 : checkPrefixCuts (2^48) 6382419969 10 Manual.Count131072.C048664.packed 64 cuts48664 = true := by
 decide +kernel
def pointBounds48664 : List (Nat × Nat × Nat) := [(6382465024,111319718168507,111320105098261)]
theorem point_links_checked48664 : (cuts48664.take 1).map (fun c => (6382419969-1+2*2^10*c.k,111319632126602+c.lower,111320019056305+c.upper)) = pointBounds48664 := by
 decide +kernel
def cuts48665 : List PrefixCut := [⟨56,224073601,224073725⟩,
⟨64,255604986,255605128⟩]
theorem checked48665 : checkPrefixCuts (2^48) 6382551041 10 Manual.Count131072.C048665.packed 64 cuts48665 = true := by
 decide +kernel
def pointBounds48665 : List (Nat × Nat × Nat) := [(6382665728,111320112295508,111320499225481)]
theorem point_links_checked48665 : (cuts48665.take 1).map (fun c => (6382551041-1+2*2^10*c.k,111319888221907+c.lower,111320275151756+c.upper)) = pointBounds48665 := by
 decide +kernel
def cuts48666 : List PrefixCut := [⟨64,253350673,253350816⟩]
theorem checked48666 : checkPrefixCuts (2^48) 6382682113 10 Manual.Count131072.C048666.packed 64 cuts48666 = true := by
 decide +kernel
def cuts48667 : List PrefixCut := [⟨26,103587830,103587887⟩,
⟨64,256432341,256432486⟩]
theorem checked48667 : checkPrefixCuts (2^48) 6382813185 10 Manual.Count131072.C048667.packed 64 cuts48667 = true := by
 decide +kernel
def pointBounds48667 : List (Nat × Nat × Nat) := [(6382866432,111320500765396,111320887695587)]
theorem point_links_checked48667 : (cuts48667.take 1).map (fun c => (6382813185-1+2*2^10*c.k,111320397177566+c.lower,111320784107700+c.upper)) = pointBounds48667 := by
 decide +kernel
def cuts48668 : List PrefixCut := [⟨60,240552122,240552258⟩,
⟨64,255280551,255280696⟩]
theorem checked48668 : checkPrefixCuts (2^48) 6382944257 10 Manual.Count131072.C048668.packed 64 cuts48668 = true := by
 decide +kernel
def pointBounds48668 : List (Nat × Nat × Nat) := [(6383067136,111320894162029,111321281092444)]
theorem point_links_checked48668 : (cuts48668.take 1).map (fun c => (6382944257-1+2*2^10*c.k,111320653609907+c.lower,111321040540186+c.upper)) = pointBounds48668 := by
 decide +kernel
def cuts48669 : List PrefixCut := [⟨64,255010705,255010852⟩]
theorem checked48669 : checkPrefixCuts (2^48) 6383075329 10 Manual.Count131072.C048669.packed 64 cuts48669 = true := by
 decide +kernel
def cuts48670 : List PrefixCut := [⟨30,118838579,118838646⟩,
⟨64,254211748,254211893⟩]
theorem checked48670 : checkPrefixCuts (2^48) 6383206401 10 Manual.Count131072.C048670.packed 64 cuts48670 = true := by
 decide +kernel
def pointBounds48670 : List (Nat × Nat × Nat) := [(6383267840,111321282739742,111321669670380)]
theorem point_links_checked48670 : (cuts48670.take 1).map (fun c => (6383206401-1+2*2^10*c.k,111321163901163+c.lower,111321550831734+c.upper)) = pointBounds48670 := by
 decide +kernel
def cuts48671 : List PrefixCut := [⟨64,253324649,253324800⟩]
theorem checked48671 : checkPrefixCuts (2^48) 6383337473 10 Manual.Count131072.C048671.packed 64 cuts48671 = true := by
 decide +kernel
def pointBounds48671 : List (Nat × Nat × Nat) := [(6383468544,111321671437560,111322058368427)]
theorem point_links_checked48671 : (cuts48671.take 1).map (fun c => (6383337473-1+2*2^10*c.k,111321418112911+c.lower,111321805043627+c.upper)) = pointBounds48671 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000270
