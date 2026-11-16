import PlattAssemblyKernel
import PlattCertificates.Count131072.C052688
import PlattCertificates.Count131072.C052689
import PlattCertificates.Count131072.C052690
import PlattCertificates.Count131072.C052691
import PlattCertificates.Count131072.C052692
import PlattCertificates.Count131072.C052693
import PlattCertificates.Count131072.C052694
import PlattCertificates.Count131072.C052695
import PlattCertificates.Count131072.C052696
import PlattCertificates.Count131072.C052697
import PlattCertificates.Count131072.C052698
import PlattCertificates.Count131072.C052699
import PlattCertificates.Count131072.C052700
import PlattCertificates.Count131072.C052701
import PlattCertificates.Count131072.C052702
import PlattCertificates.Count131072.C052703
import PlattCertificates.Count131072.C052704
import PlattCertificates.Count131072.C052705
import PlattCertificates.Count131072.C052706
import PlattCertificates.Count131072.C052707
import PlattCertificates.Count131072.C052708
import PlattCertificates.Count131072.C052709
import PlattCertificates.Count131072.C052710
import PlattCertificates.Count131072.C052711
import PlattCertificates.Count131072.C052712
import PlattCertificates.Count131072.C052713
import PlattCertificates.Count131072.C052714
import PlattCertificates.Count131072.C052715
import PlattCertificates.Count131072.C052716
import PlattCertificates.Count131072.C052717
import PlattCertificates.Count131072.C052718
import PlattCertificates.Count131072.C052719
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000084
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts52688 : List PrefixCut := [⟨64,235203330,235203464⟩]
theorem checked52688 : checkPrefixCuts (2^48) 6909853697 10 Manual.Count131072.C052688.packed 64 cuts52688 = true := by
 decide +kernel
def cuts52689 : List PrefixCut := [⟨20,72344287,72344329⟩,
⟨64,233447289,233447425⟩]
theorem checked52689 : checkPrefixCuts (2^48) 6909984769 10 Manual.Count131072.C052689.packed 64 cuts52689 = true := by
 decide +kernel
def pointBounds52689 : List (Nat × Nat × Nat) := [(6910025728,112308101615576,112308489107918)]
theorem point_links_checked52689 : (cuts52689.take 1).map (fun c => (6909984769-1+2*2^10*c.k,112308029271289+c.lower,112308416763589+c.upper)) = pointBounds52689 := by
 decide +kernel
def cuts52690 : List PrefixCut := [⟨62,227618090,227618217⟩,
⟨64,235112959,235113090⟩]
theorem checked52690 : checkPrefixCuts (2^48) 6910115841 10 Manual.Count131072.C052690.packed 64 cuts52690 = true := by
 decide +kernel
def pointBounds52690 : List (Nat × Nat × Nat) := [(6910242816,112308490336668,112308877829231)]
theorem point_links_checked52690 : (cuts52690.take 1).map (fun c => (6910115841-1+2*2^10*c.k,112308262718578+c.lower,112308650211014+c.upper)) = pointBounds52690 := by
 decide +kernel
def cuts52691 : List PrefixCut := [⟨64,238163410,238163545⟩]
theorem checked52691 : checkPrefixCuts (2^48) 6910246913 10 Manual.Count131072.C052691.packed 64 cuts52691 = true := by
 decide +kernel
def cuts52692 : List PrefixCut := [⟨40,147938465,147938551⟩,
⟨64,233922809,233922945⟩]
theorem checked52692 : checkPrefixCuts (2^48) 6910377985 10 Manual.Count131072.C052692.packed 64 cuts52692 = true := by
 decide +kernel
def pointBounds52692 : List (Nat × Nat × Nat) := [(6910459904,112308883933412,112309271426200)]
theorem point_links_checked52692 : (cuts52692.take 1).map (fun c => (6910377985-1+2*2^10*c.k,112308735994947+c.lower,112309123487649+c.upper)) = pointBounds52692 := by
 decide +kernel
def cuts52693 : List PrefixCut := [⟨64,236158582,236158713⟩]
theorem checked52693 : checkPrefixCuts (2^48) 6910509057 10 Manual.Count131072.C052693.packed 64 cuts52693 = true := by
 decide +kernel
def cuts52694 : List PrefixCut := [⟨18,67083211,67083248⟩,
⟨64,238842307,238842439⟩]
theorem checked52694 : checkPrefixCuts (2^48) 6910640129 10 Manual.Count131072.C052694.packed 64 cuts52694 = true := by
 decide +kernel
def pointBounds52694 : List (Nat × Nat × Nat) := [(6910676992,112309273159549,112309660652555)]
theorem point_links_checked52694 : (cuts52694.take 1).map (fun c => (6910640129-1+2*2^10*c.k,112309206076338+c.lower,112309593569307+c.upper)) = pointBounds52694 := by
 decide +kernel
def cuts52695 : List PrefixCut := [⟨60,226130309,226130439⟩,
⟨64,240996443,240996581⟩]
theorem checked52695 : checkPrefixCuts (2^48) 6910771201 10 Manual.Count131072.C052695.packed 64 cuts52695 = true := by
 decide +kernel
def pointBounds52695 : List (Nat × Nat × Nat) := [(6910894080,112309671048954,112310058542185)]
theorem point_links_checked52695 : (cuts52695.take 1).map (fun c => (6910771201-1+2*2^10*c.k,112309444918645+c.lower,112309832411746+c.upper)) = pointBounds52695 := by
 decide +kernel
def cuts52696 : List PrefixCut := [⟨64,234882554,234882684⟩]
theorem checked52696 : checkPrefixCuts (2^48) 6910902273 10 Manual.Count131072.C052696.packed 64 cuts52696 = true := by
 decide +kernel
def cuts52697 : List PrefixCut := [⟨38,141937453,141937532⟩,
⟨64,237281047,237281178⟩]
theorem checked52697 : checkPrefixCuts (2^48) 6911033345 10 Manual.Count131072.C052697.packed 64 cuts52697 = true := by
 decide +kernel
def pointBounds52697 : List (Nat × Nat × Nat) := [(6911111168,112310062735095,112310450228543)]
theorem point_links_checked52697 : (cuts52697.take 1).map (fun c => (6911033345-1+2*2^10*c.k,112309920797642+c.lower,112310308291011+c.upper)) = pointBounds52697 := by
 decide +kernel
def cuts52698 : List PrefixCut := [⟨64,235891814,235891947⟩]
theorem checked52698 : checkPrefixCuts (2^48) 6911164417 10 Manual.Count131072.C052698.packed 64 cuts52698 = true := by
 decide +kernel
def cuts52699 : List PrefixCut := [⟨16,60356966,60356998⟩,
⟨64,238330947,238331085⟩]
theorem checked52699 : checkPrefixCuts (2^48) 6911295489 10 Manual.Count131072.C052699.packed 64 cuts52699 = true := by
 decide +kernel
def pointBounds52699 : List (Nat × Nat × Nat) := [(6911328256,112310454327469,112310841821134)]
theorem point_links_checked52699 : (cuts52699.take 1).map (fun c => (6911295489-1+2*2^10*c.k,112310393970503+c.lower,112310781464136+c.upper)) = pointBounds52699 := by
 decide +kernel
def cuts52700 : List PrefixCut := [⟨58,213524680,213524801⟩,
⟨64,235027629,235027762⟩]
theorem checked52700 : checkPrefixCuts (2^48) 6911426561 10 Manual.Count131072.C052700.packed 64 cuts52700 = true := by
 decide +kernel
def pointBounds52700 : List (Nat × Nat × Nat) := [(6911545344,112310845826130,112311233320022)]
theorem point_links_checked52700 : (cuts52700.take 1).map (fun c => (6911426561-1+2*2^10*c.k,112310632301450+c.lower,112311019795221+c.upper)) = pointBounds52700 := by
 decide +kernel
def cuts52701 : List PrefixCut := [⟨64,234941731,234941863⟩]
theorem checked52701 : checkPrefixCuts (2^48) 6911557633 10 Manual.Count131072.C052701.packed 64 cuts52701 = true := by
 decide +kernel
def cuts52702 : List PrefixCut := [⟨36,131091386,131091459⟩,
⟨64,233756265,233756397⟩]
theorem checked52702 : checkPrefixCuts (2^48) 6911688705 10 Manual.Count131072.C052702.packed 64 cuts52702 = true := by
 decide +kernel
def pointBounds52702 : List (Nat × Nat × Nat) := [(6911762432,112311233362196,112311620856305)]
theorem point_links_checked52702 : (cuts52702.take 1).map (fun c => (6911688705-1+2*2^10*c.k,112311102270810+c.lower,112311489764846+c.upper)) = pointBounds52702 := by
 decide +kernel
def cuts52703 : List PrefixCut := [⟨64,235665814,235665951⟩]
theorem checked52703 : checkPrefixCuts (2^48) 6911819777 10 Manual.Count131072.C052703.packed 64 cuts52703 = true := by
 decide +kernel
def cuts52704 : List PrefixCut := [⟨14,50170548,50170576⟩,
⟨64,235254143,235254274⟩]
theorem checked52704 : checkPrefixCuts (2^48) 6911950849 10 Manual.Count131072.C052704.packed 64 cuts52704 = true := by
 decide +kernel
def pointBounds52704 : List (Nat × Nat × Nat) := [(6911979520,112311621863437,112312009357770)]
theorem point_links_checked52704 : (cuts52704.take 1).map (fun c => (6911950849-1+2*2^10*c.k,112311571692889+c.lower,112311959187194+c.upper)) = pointBounds52704 := by
 decide +kernel
def cuts52705 : List PrefixCut := [⟨56,205970965,205971079⟩,
⟨64,235127510,235127640⟩]
theorem checked52705 : checkPrefixCuts (2^48) 6912081921 10 Manual.Count131072.C052705.packed 64 cuts52705 = true := by
 decide +kernel
def pointBounds52705 : List (Nat × Nat × Nat) := [(6912196608,112312012917997,112312400412547)]
theorem point_links_checked52705 : (cuts52705.take 1).map (fun c => (6912081921-1+2*2^10*c.k,112311806947032+c.lower,112312194441468+c.upper)) = pointBounds52705 := by
 decide +kernel
def cuts52706 : List PrefixCut := [⟨64,235570971,235571105⟩]
theorem checked52706 : checkPrefixCuts (2^48) 6912212993 10 Manual.Count131072.C052706.packed 64 cuts52706 = true := by
 decide +kernel
def cuts52707 : List PrefixCut := [⟨34,123301397,123301468⟩,
⟨64,233041857,233041989⟩]
theorem checked52707 : checkPrefixCuts (2^48) 6912344065 10 Manual.Count131072.C052707.packed 64 cuts52707 = true := by
 decide +kernel
def pointBounds52707 : List (Nat × Nat × Nat) := [(6912413696,112312400946910,112312788441681)]
theorem point_links_checked52707 : (cuts52707.take 1).map (fun c => (6912344065-1+2*2^10*c.k,112312277645513+c.lower,112312665140213+c.upper)) = pointBounds52707 := by
 decide +kernel
def cuts52708 : List PrefixCut := [⟨64,235521326,235521457⟩]
theorem checked52708 : checkPrefixCuts (2^48) 6912475137 10 Manual.Count131072.C052708.packed 64 cuts52708 = true := by
 decide +kernel
def cuts52709 : List PrefixCut := [⟨12,42917823,42917847⟩,
⟨64,232585132,232585260⟩]
theorem checked52709 : checkPrefixCuts (2^48) 6912606209 10 Manual.Count131072.C052709.packed 64 cuts52709 = true := by
 decide +kernel
def pointBounds52709 : List (Nat × Nat × Nat) := [(6912630784,112312789126519,112313176621506)]
theorem point_links_checked52709 : (cuts52709.take 1).map (fun c => (6912606209-1+2*2^10*c.k,112312746208696+c.lower,112313133703659+c.upper)) = pointBounds52709 := by
 decide +kernel
def cuts52710 : List PrefixCut := [⟨54,201391083,201391195⟩,
⟨64,237874041,237874174⟩]
theorem checked52710 : checkPrefixCuts (2^48) 6912737281 10 Manual.Count131072.C052710.packed 64 cuts52710 = true := by
 decide +kernel
def pointBounds52710 : List (Nat × Nat × Nat) := [(6912847872,112313180184911,112313567680114)]
theorem point_links_checked52710 : (cuts52710.take 1).map (fun c => (6912737281-1+2*2^10*c.k,112312978793828+c.lower,112313366288919+c.upper)) = pointBounds52710 := by
 decide +kernel
def cuts52711 : List PrefixCut := [⟨64,233146340,233146472⟩]
theorem checked52711 : checkPrefixCuts (2^48) 6912868353 10 Manual.Count131072.C052711.packed 64 cuts52711 = true := by
 decide +kernel
def cuts52712 : List PrefixCut := [⟨32,115146433,115146500⟩,
⟨64,233834079,233834214⟩]
theorem checked52712 : checkPrefixCuts (2^48) 6912999425 10 Manual.Count131072.C052712.packed 64 cuts52712 = true := by
 decide +kernel
def pointBounds52712 : List (Nat × Nat × Nat) := [(6913064960,112313564960642,112313952456065)]
theorem point_links_checked52712 : (cuts52712.take 1).map (fun c => (6912999425-1+2*2^10*c.k,112313449814209+c.lower,112313837309565+c.upper)) = pointBounds52712 := by
 decide +kernel
def cuts52713 : List PrefixCut := [⟨64,235051149,235051281⟩]
theorem checked52713 : checkPrefixCuts (2^48) 6913130497 10 Manual.Count131072.C052713.packed 64 cuts52713 = true := by
 decide +kernel
def cuts52714 : List PrefixCut := [⟨10,37295077,37295097⟩,
⟨64,236512412,236512544⟩]
theorem checked52714 : checkPrefixCuts (2^48) 6913261569 10 Manual.Count131072.C052714.packed 64 cuts52714 = true := by
 decide +kernel
def pointBounds52714 : List (Nat × Nat × Nat) := [(6913282048,112313955994514,112314343490157)]
theorem point_links_checked52714 : (cuts52714.take 1).map (fun c => (6913261569-1+2*2^10*c.k,112313918699437+c.lower,112314306195060+c.upper)) = pointBounds52714 := by
 decide +kernel
def cuts52715 : List PrefixCut := [⟨52,190257122,190257226⟩,
⟨64,235082946,235083076⟩]
theorem checked52715 : checkPrefixCuts (2^48) 6913392641 10 Manual.Count131072.C052715.packed 64 cuts52715 = true := by
 decide +kernel
def pointBounds52715 : List (Nat × Nat × Nat) := [(6913499136,112314345468971,112314732964830)]
theorem point_links_checked52715 : (cuts52715.take 1).map (fun c => (6913392641-1+2*2^10*c.k,112314155211849+c.lower,112314542707604+c.upper)) = pointBounds52715 := by
 decide +kernel
def cuts52716 : List PrefixCut := [⟨64,235648453,235648591⟩]
theorem checked52716 : checkPrefixCuts (2^48) 6913523713 10 Manual.Count131072.C052716.packed 64 cuts52716 = true := by
 decide +kernel
def cuts52717 : List PrefixCut := [⟨30,110453592,110453653⟩,
⟨64,236539672,236539804⟩]
theorem checked52717 : checkPrefixCuts (2^48) 6913654785 10 Manual.Count131072.C052717.packed 64 cuts52717 = true := by
 decide +kernel
def pointBounds52717 : List (Nat × Nat × Nat) := [(6913716224,112314736396840,112315123892924)]
theorem point_links_checked52717 : (cuts52717.take 1).map (fun c => (6913654785-1+2*2^10*c.k,112314625943248+c.lower,112315013439271+c.upper)) = pointBounds52717 := by
 decide +kernel
def cuts52718 : List PrefixCut := [⟨64,234784594,234784726⟩]
theorem checked52718 : checkPrefixCuts (2^48) 6913785857 10 Manual.Count131072.C052718.packed 64 cuts52718 = true := by
 decide +kernel
def cuts52719 : List PrefixCut := [⟨8,27561553,27561569⟩,
⟨64,233965920,233966057⟩]
theorem checked52719 : checkPrefixCuts (2^48) 6913916929 10 Manual.Count131072.C052719.packed 64 cuts52719 = true := by
 decide +kernel
def pointBounds52719 : List (Nat × Nat × Nat) := [(6913933312,112315124829067,112315512325370)]
theorem point_links_checked52719 : (cuts52719.take 1).map (fun c => (6913916929-1+2*2^10*c.k,112315097267514+c.lower,112315484763801+c.upper)) = pointBounds52719 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000084
