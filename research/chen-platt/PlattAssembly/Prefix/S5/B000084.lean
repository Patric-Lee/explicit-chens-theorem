import PlattAssemblyKernel
import PlattCertificates.Count131072.C042688
import PlattCertificates.Count131072.C042689
import PlattCertificates.Count131072.C042690
import PlattCertificates.Count131072.C042691
import PlattCertificates.Count131072.C042692
import PlattCertificates.Count131072.C042693
import PlattCertificates.Count131072.C042694
import PlattCertificates.Count131072.C042695
import PlattCertificates.Count131072.C042696
import PlattCertificates.Count131072.C042697
import PlattCertificates.Count131072.C042698
import PlattCertificates.Count131072.C042699
import PlattCertificates.Count131072.C042700
import PlattCertificates.Count131072.C042701
import PlattCertificates.Count131072.C042702
import PlattCertificates.Count131072.C042703
import PlattCertificates.Count131072.C042704
import PlattCertificates.Count131072.C042705
import PlattCertificates.Count131072.C042706
import PlattCertificates.Count131072.C042707
import PlattCertificates.Count131072.C042708
import PlattCertificates.Count131072.C042709
import PlattCertificates.Count131072.C042710
import PlattCertificates.Count131072.C042711
import PlattCertificates.Count131072.C042712
import PlattCertificates.Count131072.C042713
import PlattCertificates.Count131072.C042714
import PlattCertificates.Count131072.C042715
import PlattCertificates.Count131072.C042716
import PlattCertificates.Count131072.C042717
import PlattCertificates.Count131072.C042718
import PlattCertificates.Count131072.C042719
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000084
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts42688 : List PrefixCut := [⟨42,190325124,190325235⟩,
⟨64,292273047,292273220⟩]
theorem checked42688 : checkPrefixCuts (2^48) 5599133697 10 Manual.Count131072.C042688.packed 64 cuts42688 = true := by
 decide +kernel
def pointBounds42688 : List (Nat × Nat × Nat) := [(5599219712,109682592420268,109682978406580)]
theorem point_links_checked42688 : (cuts42688.take 1).map (fun c => (5599133697-1+2*2^10*c.k,109682402095144+c.lower,109682788081345+c.upper)) = pointBounds42688 := by
 decide +kernel
def cuts42689 : List PrefixCut := [⟨64,293874801,293874978⟩]
theorem checked42689 : checkPrefixCuts (2^48) 5599264769 10 Manual.Count131072.C042689.packed 64 cuts42689 = true := by
 decide +kernel
def pointBounds42689 : List (Nat × Nat × Nat) := [(5599395840,109682988242992,109683374229543)]
theorem point_links_checked42689 : (cuts42689.take 1).map (fun c => (5599264769-1+2*2^10*c.k,109682694368191+c.lower,109683080354565+c.upper)) = pointBounds42689 := by
 decide +kernel
def cuts42690 : List PrefixCut := [⟨64,292309614,292309786⟩]
theorem checked42690 : checkPrefixCuts (2^48) 5599395841 10 Manual.Count131072.C042690.packed 64 cuts42690 = true := by
 decide +kernel
def cuts42691 : List PrefixCut := [⟨22,102344464,102344525⟩,
⟨64,293509225,293509399⟩]
theorem checked42691 : checkPrefixCuts (2^48) 5599526913 10 Manual.Count131072.C042691.packed 64 cuts42691 = true := by
 decide +kernel
def pointBounds42691 : List (Nat × Nat × Nat) := [(5599571968,109683382897070,109683768883854)]
theorem point_links_checked42691 : (cuts42691.take 1).map (fun c => (5599526913-1+2*2^10*c.k,109683280552606+c.lower,109683666539329+c.upper)) = pointBounds42691 := by
 decide +kernel
def cuts42692 : List PrefixCut := [⟨44,201214960,201215076⟩,
⟨64,292899140,292899312⟩]
theorem checked42692 : checkPrefixCuts (2^48) 5599657985 10 Manual.Count131072.C042692.packed 64 cuts42692 = true := by
 decide +kernel
def pointBounds42692 : List (Nat × Nat × Nat) := [(5599748096,109683775276791,109684161263804)]
theorem point_links_checked42692 : (cuts42692.take 1).map (fun c => (5599657985-1+2*2^10*c.k,109683574061831+c.lower,109683960048728+c.upper)) = pointBounds42692 := by
 decide +kernel
def cuts42693 : List PrefixCut := [⟨64,294902887,294903063⟩]
theorem checked42693 : checkPrefixCuts (2^48) 5599789057 10 Manual.Count131072.C042693.packed 64 cuts42693 = true := by
 decide +kernel
def cuts42694 : List PrefixCut := [⟨2,8997269,8997274⟩,
⟨64,291930444,291930611⟩]
theorem checked42694 : checkPrefixCuts (2^48) 5599920129 10 Manual.Count131072.C042694.packed 64 cuts42694 = true := by
 decide +kernel
def pointBounds42694 : List (Nat × Nat × Nat) := [(5599924224,109684170861127,109684556848377)]
theorem point_links_checked42694 : (cuts42694.take 1).map (fun c => (5599920129-1+2*2^10*c.k,109684161863858+c.lower,109684547851103+c.upper)) = pointBounds42694 := by
 decide +kernel
def cuts42695 : List PrefixCut := [⟨24,108466893,108466953⟩,
⟨64,295894276,295894446⟩]
theorem checked42695 : checkPrefixCuts (2^48) 5600051201 10 Manual.Count131072.C042695.packed 64 cuts42695 = true := by
 decide +kernel
def pointBounds42695 : List (Nat × Nat × Nat) := [(5600100352,109684562261195,109684948248667)]
theorem point_links_checked42695 : (cuts42695.take 1).map (fun c => (5600051201-1+2*2^10*c.k,109684453794302+c.lower,109684839781714+c.upper)) = pointBounds42695 := by
 decide +kernel
def cuts42696 : List PrefixCut := [⟨46,212153011,212153132⟩,
⟨64,296591032,296591203⟩]
theorem checked42696 : checkPrefixCuts (2^48) 5600182273 10 Manual.Count131072.C042696.packed 64 cuts42696 = true := by
 decide +kernel
def pointBounds42696 : List (Nat × Nat × Nat) := [(5600276480,109684961841589,109685347829292)]
theorem point_links_checked42696 : (cuts42696.take 1).map (fun c => (5600182273-1+2*2^10*c.k,109684749688578+c.lower,109685135676160+c.upper)) = pointBounds42696 := by
 decide +kernel
def cuts42697 : List PrefixCut := [⟨64,295528668,295528845⟩]
theorem checked42697 : checkPrefixCuts (2^48) 5600313345 10 Manual.Count131072.C042697.packed 64 cuts42697 = true := by
 decide +kernel
def cuts42698 : List PrefixCut := [⟨4,18143625,18143636⟩,
⟨64,290646652,290646829⟩]
theorem checked42698 : checkPrefixCuts (2^48) 5600444417 10 Manual.Count131072.C042698.packed 64 cuts42698 = true := by
 decide +kernel
def pointBounds42698 : List (Nat × Nat × Nat) := [(5600452608,109685359951903,109685745939844)]
theorem point_links_checked42698 : (cuts42698.take 1).map (fun c => (5600444417-1+2*2^10*c.k,109685341808278+c.lower,109685727796208+c.upper)) = pointBounds42698 := by
 decide +kernel
def cuts42699 : List PrefixCut := [⟨26,120669385,120669455⟩,
⟨64,293001939,293002109⟩]
theorem checked42699 : checkPrefixCuts (2^48) 5600575489 10 Manual.Count131072.C042699.packed 64 cuts42699 = true := by
 decide +kernel
def pointBounds42699 : List (Nat × Nat × Nat) := [(5600628736,109685753124315,109686139112492)]
theorem point_links_checked42699 : (cuts42699.take 1).map (fun c => (5600575489-1+2*2^10*c.k,109685632454930+c.lower,109686018443037+c.upper)) = pointBounds42699 := by
 decide +kernel
def cuts42700 : List PrefixCut := [⟨48,218917722,218917843⟩,
⟨64,290683296,290683462⟩]
theorem checked42700 : checkPrefixCuts (2^48) 5600706561 10 Manual.Count131072.C042700.packed 64 cuts42700 = true := by
 decide +kernel
def pointBounds42700 : List (Nat × Nat × Nat) := [(5600804864,109686144374591,109686530362989)]
theorem point_links_checked42700 : (cuts42700.take 1).map (fun c => (5600706561-1+2*2^10*c.k,109685925456869+c.lower,109686311445146+c.upper)) = pointBounds42700 := by
 decide +kernel
def cuts42701 : List PrefixCut := [⟨64,295249687,295249859⟩]
theorem checked42701 : checkPrefixCuts (2^48) 5600837633 10 Manual.Count131072.C042701.packed 64 cuts42701 = true := by
 decide +kernel
def cuts42702 : List PrefixCut := [⟨6,27941571,27941589⟩,
⟨64,296147367,296147540⟩]
theorem checked42702 : checkPrefixCuts (2^48) 5600968705 10 Manual.Count131072.C042702.packed 64 cuts42702 = true := by
 decide +kernel
def pointBounds42702 : List (Nat × Nat × Nat) := [(5600980992,109686539331423,109686925320056)]
theorem point_links_checked42702 : (cuts42702.take 1).map (fun c => (5600968705-1+2*2^10*c.k,109686511389852+c.lower,109686897378467+c.upper)) = pointBounds42702 := by
 decide +kernel
def cuts42703 : List PrefixCut := [⟨28,126889451,126889526⟩,
⟨64,293024742,293024912⟩]
theorem checked42703 : checkPrefixCuts (2^48) 5601099777 10 Manual.Count131072.C042703.packed 64 cuts42703 = true := by
 decide +kernel
def pointBounds42703 : List (Nat × Nat × Nat) := [(5601157120,109686934426670,109687320415533)]
theorem point_links_checked42703 : (cuts42703.take 1).map (fun c => (5601099777-1+2*2^10*c.k,109686807537219+c.lower,109687193526007+c.upper)) = pointBounds42703 := by
 decide +kernel
def cuts42704 : List PrefixCut := [⟨50,229550544,229550684⟩,
⟨64,293520424,293520602⟩]
theorem checked42704 : checkPrefixCuts (2^48) 5601230849 10 Manual.Count131072.C042704.packed 64 cuts42704 = true := by
 decide +kernel
def pointBounds42704 : List (Nat × Nat × Nat) := [(5601333248,109687330112505,109687716101603)]
theorem point_links_checked42704 : (cuts42704.take 1).map (fun c => (5601230849-1+2*2^10*c.k,109687100561961+c.lower,109687486550919+c.upper)) = pointBounds42704 := by
 decide +kernel
def cuts42705 : List PrefixCut := [⟨64,291654274,291654439⟩]
theorem checked42705 : checkPrefixCuts (2^48) 5601361921 10 Manual.Count131072.C042705.packed 64 cuts42705 = true := by
 decide +kernel
def cuts42706 : List PrefixCut := [⟨8,37335679,37335700⟩,
⟨64,293104700,293104872⟩]
theorem checked42706 : checkPrefixCuts (2^48) 5601492993 10 Manual.Count131072.C042706.packed 64 cuts42706 = true := by
 decide +kernel
def pointBounds42706 : List (Nat × Nat × Nat) := [(5601509376,109687723072338,109688109061660)]
theorem point_links_checked42706 : (cuts42706.take 1).map (fun c => (5601492993-1+2*2^10*c.k,109687685736659+c.lower,109688071725960+c.upper)) = pointBounds42706 := by
 decide +kernel
def cuts42707 : List PrefixCut := [⟨30,138334187,138334265⟩,
⟨64,295559984,295560151⟩]
theorem checked42707 : checkPrefixCuts (2^48) 5601624065 10 Manual.Count131072.C042707.packed 64 cuts42707 = true := by
 decide +kernel
def pointBounds42707 : List (Nat × Nat × Nat) := [(5601685504,109688117175546,109688503165097)]
theorem point_links_checked42707 : (cuts42707.take 1).map (fun c => (5601624065-1+2*2^10*c.k,109687978841359+c.lower,109688364830832+c.upper)) = pointBounds42707 := by
 decide +kernel
def cuts42708 : List PrefixCut := [⟨52,240181380,240181519⟩,
⟨64,294698898,294699068⟩]
theorem checked42708 : checkPrefixCuts (2^48) 5601755137 10 Manual.Count131072.C042708.packed 64 cuts42708 = true := by
 decide +kernel
def pointBounds42708 : List (Nat × Nat × Nat) := [(5601861632,109688514582723,109688900572502)]
theorem point_links_checked42708 : (cuts42708.take 1).map (fun c => (5601755137-1+2*2^10*c.k,109688274401343+c.lower,109688660390983+c.upper)) = pointBounds42708 := by
 decide +kernel
def cuts42709 : List PrefixCut := [⟨64,293335346,293335523⟩]
theorem checked42709 : checkPrefixCuts (2^48) 5601886209 10 Manual.Count131072.C042709.packed 64 cuts42709 = true := by
 decide +kernel
def cuts42710 : List PrefixCut := [⟨10,45522135,45522161⟩,
⟨64,291368941,291369108⟩]
theorem checked42710 : checkPrefixCuts (2^48) 5602017281 10 Manual.Count131072.C042710.packed 64 cuts42710 = true := by
 decide +kernel
def pointBounds42710 : List (Nat × Nat × Nat) := [(5602037760,109688907957722,109689293947735)]
theorem point_links_checked42710 : (cuts42710.take 1).map (fun c => (5602017281-1+2*2^10*c.k,109688862435587+c.lower,109689248425574+c.upper)) = pointBounds42710 := by
 decide +kernel
def cuts42711 : List PrefixCut := [⟨32,146862644,146862731⟩,
⟨64,291512867,291513040⟩]
theorem checked42711 : checkPrefixCuts (2^48) 5602148353 10 Manual.Count131072.C042711.packed 64 cuts42711 = true := by
 decide +kernel
def pointBounds42711 : List (Nat × Nat × Nat) := [(5602213888,109689300667172,109689686657413)]
theorem point_links_checked42711 : (cuts42711.take 1).map (fun c => (5602148353-1+2*2^10*c.k,109689153804528+c.lower,109689539794682+c.upper)) = pointBounds42711 := by
 decide +kernel
def cuts42712 : List PrefixCut := [⟨54,240460255,240460397⟩,
⟨64,287235408,287235576⟩]
theorem checked42712 : checkPrefixCuts (2^48) 5602279425 10 Manual.Count131072.C042712.packed 64 cuts42712 = true := by
 decide +kernel
def pointBounds42712 : List (Nat × Nat × Nat) := [(5602390016,109689685777650,109690071768119)]
theorem point_links_checked42712 : (cuts42712.take 1).map (fun c => (5602279425-1+2*2^10*c.k,109689445317395+c.lower,109689831307722+c.upper)) = pointBounds42712 := by
 decide +kernel
def cuts42713 : List PrefixCut := [⟨64,289539809,289539981⟩]
theorem checked42713 : checkPrefixCuts (2^48) 5602410497 10 Manual.Count131072.C042713.packed 64 cuts42713 = true := by
 decide +kernel
def cuts42714 : List PrefixCut := [⟨12,55967873,55967906⟩,
⟨64,296365653,296365830⟩]
theorem checked42714 : checkPrefixCuts (2^48) 5602541569 10 Manual.Count131072.C042714.packed 64 cuts42714 = true := by
 decide +kernel
def pointBounds42714 : List (Nat × Nat × Nat) := [(5602566144,109690078060485,109690464051185)]
theorem point_links_checked42714 : (cuts42714.take 1).map (fun c => (5602541569-1+2*2^10*c.k,109690022092612+c.lower,109690408083279+c.upper)) = pointBounds42714 := by
 decide +kernel
def cuts42715 : List PrefixCut := [⟨34,151772272,151772361⟩,
⟨64,290179334,290179505⟩]
theorem checked42715 : checkPrefixCuts (2^48) 5602672641 10 Manual.Count131072.C042715.packed 64 cuts42715 = true := by
 decide +kernel
def pointBounds42715 : List (Nat × Nat × Nat) := [(5602742272,109690470230537,109690856221470)]
theorem point_links_checked42715 : (cuts42715.take 1).map (fun c => (5602672641-1+2*2^10*c.k,109690318458265+c.lower,109690704449109+c.upper)) = pointBounds42715 := by
 decide +kernel
def cuts42716 : List PrefixCut := [⟨56,254906143,254906294⟩,
⟨64,292483510,292483683⟩]
theorem checked42716 : checkPrefixCuts (2^48) 5602803713 10 Manual.Count131072.C042716.packed 64 cuts42716 = true := by
 decide +kernel
def pointBounds42716 : List (Nat × Nat × Nat) := [(5602918400,109690863543742,109691249534908)]
theorem point_links_checked42716 : (cuts42716.take 1).map (fun c => (5602803713-1+2*2^10*c.k,109690608637599+c.lower,109690994628614+c.upper)) = pointBounds42716 := by
 decide +kernel
def cuts42717 : List PrefixCut := [⟨64,290768621,290768787⟩]
theorem checked42717 : checkPrefixCuts (2^48) 5602934785 10 Manual.Count131072.C042717.packed 64 cuts42717 = true := by
 decide +kernel
def cuts42718 : List PrefixCut := [⟨14,66914008,66914048⟩,
⟨64,298347375,298347543⟩]
theorem checked42718 : checkPrefixCuts (2^48) 5603065857 10 Manual.Count131072.C042718.packed 64 cuts42718 = true := by
 decide +kernel
def pointBounds42718 : List (Nat × Nat × Nat) := [(5603094528,109691258803738,109691644795132)]
theorem point_links_checked42718 : (cuts42718.take 1).map (fun c => (5603065857-1+2*2^10*c.k,109691191889730+c.lower,109691577881084+c.upper)) = pointBounds42718 := by
 decide +kernel
def cuts42719 : List PrefixCut := [⟨36,162156531,162156626⟩,
⟨64,290453596,290453764⟩]
theorem checked42719 : checkPrefixCuts (2^48) 5603196929 10 Manual.Count131072.C042719.packed 64 cuts42719 = true := by
 decide +kernel
def pointBounds42719 : List (Nat × Nat × Nat) := [(5603270656,109691652393636,109692038385253)]
theorem point_links_checked42719 : (cuts42719.take 1).map (fun c => (5603196929-1+2*2^10*c.k,109691490237105+c.lower,109691876228627+c.upper)) = pointBounds42719 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000084
