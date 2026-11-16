import PlattAssemblyKernel
import PlattCertificates.Count131072.C066784
import PlattCertificates.Count131072.C066785
import PlattCertificates.Count131072.C066786
import PlattCertificates.Count131072.C066787
import PlattCertificates.Count131072.C066788
import PlattCertificates.Count131072.C066789
import PlattCertificates.Count131072.C066790
import PlattCertificates.Count131072.C066791
import PlattCertificates.Count131072.C066792
import PlattCertificates.Count131072.C066793
import PlattCertificates.Count131072.C066794
import PlattCertificates.Count131072.C066795
import PlattCertificates.Count131072.C066796
import PlattCertificates.Count131072.C066797
import PlattCertificates.Count131072.C066798
import PlattCertificates.Count131072.C066799
import PlattCertificates.Count131072.C066800
import PlattCertificates.Count131072.C066801
import PlattCertificates.Count131072.C066802
import PlattCertificates.Count131072.C066803
import PlattCertificates.Count131072.C066804
import PlattCertificates.Count131072.C066805
import PlattCertificates.Count131072.C066806
import PlattCertificates.Count131072.C066807
import PlattCertificates.Count131072.C066808
import PlattCertificates.Count131072.C066809
import PlattCertificates.Count131072.C066810
import PlattCertificates.Count131072.C066811
import PlattCertificates.Count131072.C066812
import PlattCertificates.Count131072.C066813
import PlattCertificates.Count131072.C066814
import PlattCertificates.Count131072.C066815
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000212
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts66784 : List PrefixCut := [⟨64,182849993,182850106⟩]
theorem checked66784 : checkPrefixCuts (2^48) 8757444609 10 Manual.Count131072.C066784.packed 64 cuts66784 = true := by
 decide +kernel
def cuts66785 : List PrefixCut := [⟨52,150546273,150546361⟩,
⟨64,183650777,183650886⟩]
theorem checked66785 : checkPrefixCuts (2^48) 8757575681 10 Manual.Count131072.C066785.packed 64 cuts66785 = true := by
 decide +kernel
def pointBounds66785 : List (Nat × Nat × Nat) := [(8757682176,115236679812786,115237068980206)]
theorem point_links_checked66785 : (cuts66785.take 1).map (fun c => (8757575681-1+2*2^10*c.k,115236529266513+c.lower,115236918433845+c.upper)) = pointBounds66785 := by
 decide +kernel
def cuts66786 : List PrefixCut := [⟨64,183808724,183808830⟩]
theorem checked66786 : checkPrefixCuts (2^48) 8757706753 10 Manual.Count131072.C066786.packed 64 cuts66786 = true := by
 decide +kernel
def cuts66787 : List PrefixCut := [⟨58,166129345,166129437⟩,
⟨64,183870246,183870347⟩]
theorem checked66787 : checkPrefixCuts (2^48) 8757837825 10 Manual.Count131072.C066787.packed 64 cuts66787 = true := by
 decide +kernel
def pointBounds66787 : List (Nat × Nat × Nat) := [(8757956608,115237062855359,115237452022998)]
theorem point_links_checked66787 : (cuts66787.take 1).map (fun c => (8757837825-1+2*2^10*c.k,115236896726014+c.lower,115237285893561+c.upper)) = pointBounds66787 := by
 decide +kernel
def cuts66788 : List PrefixCut := [⟨64,183835348,183835457⟩]
theorem checked66788 : checkPrefixCuts (2^48) 8757968897 10 Manual.Count131072.C066788.packed 64 cuts66788 = true := by
 decide +kernel
def cuts66789 : List PrefixCut := [⟨64,181615038,181615150⟩]
theorem checked66789 : checkPrefixCuts (2^48) 8758099969 10 Manual.Count131072.C066789.packed 64 cuts66789 = true := by
 decide +kernel
def pointBounds66789 : List (Nat × Nat × Nat) := [(8758231040,115237446046646,115237835214515)]
theorem point_links_checked66789 : (cuts66789.take 1).map (fun c => (8758099969-1+2*2^10*c.k,115237264431608+c.lower,115237653599365+c.upper)) = pointBounds66789 := by
 decide +kernel
def cuts66790 : List PrefixCut := [⟨64,184376205,184376314⟩]
theorem checked66790 : checkPrefixCuts (2^48) 8758231041 10 Manual.Count131072.C066790.packed 64 cuts66790 = true := by
 decide +kernel
def cuts66791 : List PrefixCut := [⟨64,183248636,183248739⟩]
theorem checked66791 : checkPrefixCuts (2^48) 8758362113 10 Manual.Count131072.C066791.packed 64 cuts66791 = true := by
 decide +kernel
def cuts66792 : List PrefixCut := [⟨6,17450577,17450588⟩,
⟨64,183888625,183888731⟩]
theorem checked66792 : checkPrefixCuts (2^48) 8758493185 10 Manual.Count131072.C066792.packed 64 cuts66792 = true := by
 decide +kernel
def pointBounds66792 : List (Nat × Nat × Nat) := [(8758505472,115237831122064,115238220290156)]
theorem point_links_checked66792 : (cuts66792.take 1).map (fun c => (8758493185-1+2*2^10*c.k,115237813671487+c.lower,115238202839568+c.upper)) = pointBounds66792 := by
 decide +kernel
def cuts66793 : List PrefixCut := [⟨64,184625028,184625134⟩]
theorem checked66793 : checkPrefixCuts (2^48) 8758624257 10 Manual.Count131072.C066793.packed 64 cuts66793 = true := by
 decide +kernel
def cuts66794 : List PrefixCut := [⟨12,35125041,35125060⟩,
⟨64,184108083,184108190⟩]
theorem checked66794 : checkPrefixCuts (2^48) 8758755329 10 Manual.Count131072.C066794.packed 64 cuts66794 = true := by
 decide +kernel
def pointBounds66794 : List (Nat × Nat × Nat) := [(8758779904,115238217310181,115238606478493)]
theorem point_links_checked66794 : (cuts66794.take 1).map (fun c => (8758755329-1+2*2^10*c.k,115238182185140+c.lower,115238571353433+c.upper)) = pointBounds66794 := by
 decide +kernel
def cuts66795 : List PrefixCut := [⟨64,183430477,183430583⟩]
theorem checked66795 : checkPrefixCuts (2^48) 8758886401 10 Manual.Count131072.C066795.packed 64 cuts66795 = true := by
 decide +kernel
def cuts66796 : List PrefixCut := [⟨18,51480871,51480902⟩,
⟨64,182785026,182785132⟩]
theorem checked66796 : checkPrefixCuts (2^48) 8759017473 10 Manual.Count131072.C066796.packed 64 cuts66796 = true := by
 decide +kernel
def pointBounds66796 : List (Nat × Nat × Nat) := [(8759054336,115238601204571,115238990373108)]
theorem point_links_checked66796 : (cuts66796.take 1).map (fun c => (8759017473-1+2*2^10*c.k,115238549723700+c.lower,115238938892206+c.upper)) = pointBounds66796 := by
 decide +kernel
def cuts66797 : List PrefixCut := [⟨64,186092170,186092275⟩]
theorem checked66797 : checkPrefixCuts (2^48) 8759148545 10 Manual.Count131072.C066797.packed 64 cuts66797 = true := by
 decide +kernel
def cuts66798 : List PrefixCut := [⟨24,69667355,69667398⟩,
⟨64,184771876,184771986⟩]
theorem checked66798 : checkPrefixCuts (2^48) 8759279617 10 Manual.Count131072.C066798.packed 64 cuts66798 = true := by
 decide +kernel
def pointBounds66798 : List (Nat × Nat × Nat) := [(8759328768,115238988268251,115239377437011)]
theorem point_links_checked66798 : (cuts66798.take 1).map (fun c => (8759279617-1+2*2^10*c.k,115238918600896+c.lower,115239307769613+c.upper)) = pointBounds66798 := by
 decide +kernel
def cuts66799 : List PrefixCut := [⟨64,184158564,184158670⟩]
theorem checked66799 : checkPrefixCuts (2^48) 8759410689 10 Manual.Count131072.C066799.packed 64 cuts66799 = true := by
 decide +kernel
def cuts66800 : List PrefixCut := [⟨30,86535261,86535312⟩,
⟨64,183898749,183898859⟩]
theorem checked66800 : checkPrefixCuts (2^48) 8759541761 10 Manual.Count131072.C066800.packed 64 cuts66800 = true := by
 decide +kernel
def pointBounds66800 : List (Nat × Nat × Nat) := [(8759603200,115239374066597,115239763235581)]
theorem point_links_checked66800 : (cuts66800.take 1).map (fun c => (8759541761-1+2*2^10*c.k,115239287531336+c.lower,115239676700269+c.upper)) = pointBounds66800 := by
 decide +kernel
def cuts66801 : List PrefixCut := [⟨64,182610681,182610797⟩]
theorem checked66801 : checkPrefixCuts (2^48) 8759672833 10 Manual.Count131072.C066801.packed 64 cuts66801 = true := by
 decide +kernel
def cuts66802 : List PrefixCut := [⟨36,102630956,102631016⟩,
⟨64,182736484,182736588⟩]
theorem checked66802 : checkPrefixCuts (2^48) 8759803905 10 Manual.Count131072.C066802.packed 64 cuts66802 = true := by
 decide +kernel
def pointBounds66802 : List (Nat × Nat × Nat) := [(8759877632,115239756671722,115240145840941)]
theorem point_links_checked66802 : (cuts66802.take 1).map (fun c => (8759803905-1+2*2^10*c.k,115239654040766+c.lower,115240043209925+c.upper)) = pointBounds66802 := by
 decide +kernel
def cuts66803 : List PrefixCut := [⟨64,184854453,184854566⟩]
theorem checked66803 : checkPrefixCuts (2^48) 8759934977 10 Manual.Count131072.C066803.packed 64 cuts66803 = true := by
 decide +kernel
def cuts66804 : List PrefixCut := [⟨42,121681759,121681834⟩,
⟨64,184883825,184883939⟩]
theorem checked66804 : checkPrefixCuts (2^48) 8760066049 10 Manual.Count131072.C066804.packed 64 cuts66804 = true := by
 decide +kernel
def pointBounds66804 : List (Nat × Nat × Nat) := [(8760152064,115240143313462,115240532482913)]
theorem point_links_checked66804 : (cuts66804.take 1).map (fun c => (8760066049-1+2*2^10*c.k,115240021631703+c.lower,115240410801079+c.upper)) = pointBounds66804 := by
 decide +kernel
def cuts66805 : List PrefixCut := [⟨64,182631889,182631996⟩]
theorem checked66805 : checkPrefixCuts (2^48) 8760197121 10 Manual.Count131072.C066805.packed 64 cuts66805 = true := by
 decide +kernel
def cuts66806 : List PrefixCut := [⟨48,137261295,137261377⟩,
⟨64,182243591,182243701⟩]
theorem checked66806 : checkPrefixCuts (2^48) 8760328193 10 Manual.Count131072.C066806.packed 64 cuts66806 = true := by
 decide +kernel
def pointBounds66806 : List (Nat × Nat × Nat) := [(8760426496,115240526408712,115240915578391)]
theorem point_links_checked66806 : (cuts66806.take 1).map (fun c => (8760328193-1+2*2^10*c.k,115240389147417+c.lower,115240778317014+c.upper)) = pointBounds66806 := by
 decide +kernel
def cuts66807 : List PrefixCut := [⟨64,181341237,181341341⟩]
theorem checked66807 : checkPrefixCuts (2^48) 8760459265 10 Manual.Count131072.C066807.packed 64 cuts66807 = true := by
 decide +kernel
def cuts66808 : List PrefixCut := [⟨54,155474495,155474592⟩,
⟨64,183330537,183330650⟩]
theorem checked66808 : checkPrefixCuts (2^48) 8760590337 10 Manual.Count131072.C066808.packed 64 cuts66808 = true := by
 decide +kernel
def pointBounds66808 : List (Nat × Nat × Nat) := [(8760700928,115240908206740,115241297376648)]
theorem point_links_checked66808 : (cuts66808.take 1).map (fun c => (8760590337-1+2*2^10*c.k,115240752732245+c.lower,115241141902056+c.upper)) = pointBounds66808 := by
 decide +kernel
def cuts66809 : List PrefixCut := [⟨64,184355917,184356022⟩]
theorem checked66809 : checkPrefixCuts (2^48) 8760721409 10 Manual.Count131072.C066809.packed 64 cuts66809 = true := by
 decide +kernel
def cuts66810 : List PrefixCut := [⟨60,173429563,173429663⟩,
⟨64,185156373,185156478⟩]
theorem checked66810 : checkPrefixCuts (2^48) 8760852481 10 Manual.Count131072.C066810.packed 64 cuts66810 = true := by
 decide +kernel
def pointBounds66810 : List (Nat × Nat × Nat) := [(8760975360,115241293848262,115241683018391)]
theorem point_links_checked66810 : (cuts66810.take 1).map (fun c => (8760852481-1+2*2^10*c.k,115241120418699+c.lower,115241509588728+c.upper)) = pointBounds66810 := by
 decide +kernel
def cuts66811 : List PrefixCut := [⟨64,184382545,184382654⟩]
theorem checked66811 : checkPrefixCuts (2^48) 8760983553 10 Manual.Count131072.C066811.packed 64 cuts66811 = true := by
 decide +kernel
def cuts66812 : List PrefixCut := [⟨64,182387853,182387960⟩]
theorem checked66812 : checkPrefixCuts (2^48) 8761114625 10 Manual.Count131072.C066812.packed 64 cuts66812 = true := by
 decide +kernel
def cuts66813 : List PrefixCut := [⟨2,5429507,5429510⟩,
⟨64,182224491,182224598⟩]
theorem checked66813 : checkPrefixCuts (2^48) 8761245697 10 Manual.Count131072.C066813.packed 64 cuts66813 = true := by
 decide +kernel
def pointBounds66813 : List (Nat × Nat × Nat) := [(8761249792,115241677774977,115242066945330)]
theorem point_links_checked66813 : (cuts66813.take 1).map (fun c => (8761245697-1+2*2^10*c.k,115241672345470+c.lower,115242061515820+c.upper)) = pointBounds66813 := by
 decide +kernel
def cuts66814 : List PrefixCut := [⟨64,182767931,182768033⟩]
theorem checked66814 : checkPrefixCuts (2^48) 8761376769 10 Manual.Count131072.C066814.packed 64 cuts66814 = true := by
 decide +kernel
def cuts66815 : List PrefixCut := [⟨8,22745404,22745417⟩,
⟨64,183568357,183568471⟩]
theorem checked66815 : checkPrefixCuts (2^48) 8761507841 10 Manual.Count131072.C066815.packed 64 cuts66815 = true := by
 decide +kernel
def pointBounds66815 : List (Nat × Nat × Nat) := [(8761524224,115242060083296,115242449253868)]
theorem point_links_checked66815 : (cuts66815.take 1).map (fun c => (8761507841-1+2*2^10*c.k,115242037337892+c.lower,115242426508451+c.upper)) = pointBounds66815 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000212
