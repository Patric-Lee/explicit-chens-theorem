import PlattAssemblyKernel
import PlattCertificates.Count131072.C025760
import PlattCertificates.Count131072.C025761
import PlattCertificates.Count131072.C025762
import PlattCertificates.Count131072.C025763
import PlattCertificates.Count131072.C025764
import PlattCertificates.Count131072.C025765
import PlattCertificates.Count131072.C025766
import PlattCertificates.Count131072.C025767
import PlattCertificates.Count131072.C025768
import PlattCertificates.Count131072.C025769
import PlattCertificates.Count131072.C025770
import PlattCertificates.Count131072.C025771
import PlattCertificates.Count131072.C025772
import PlattCertificates.Count131072.C025773
import PlattCertificates.Count131072.C025774
import PlattCertificates.Count131072.C025775
import PlattCertificates.Count131072.C025776
import PlattCertificates.Count131072.C025777
import PlattCertificates.Count131072.C025778
import PlattCertificates.Count131072.C025779
import PlattCertificates.Count131072.C025780
import PlattCertificates.Count131072.C025781
import PlattCertificates.Count131072.C025782
import PlattCertificates.Count131072.C025783
import PlattCertificates.Count131072.C025784
import PlattCertificates.Count131072.C025785
import PlattCertificates.Count131072.C025786
import PlattCertificates.Count131072.C025787
import PlattCertificates.Count131072.C025788
import PlattCertificates.Count131072.C025789
import PlattCertificates.Count131072.C025790
import PlattCertificates.Count131072.C025791
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000180
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts25760 : List PrefixCut := [⟨14,51293008,51293038⟩,
⟨118,452303917,452304172⟩,
⟨128,494186187,494186463⟩]
theorem checked25760 : checkPrefixCuts (2^48) 3380346881 9 Manual.Count131072.C025760.packed 128 cuts25760 = true := by
 decide +kernel
def pointBounds25760 : List (Nat × Nat × Nat) := [(3380361216,103282012578555,103282394810215),(3380467712,103282413589464,103282795821349)]
theorem point_links_checked25760 : (cuts25760.take 2).map (fun c => (3380346881-1+2*2^9*c.k,103281961285547+c.lower,103282343517177+c.upper)) = pointBounds25760 := by
 decide +kernel
def cuts25761 : List PrefixCut := [⟨94,362446612,362446819⟩,
⟨128,495416063,495416345⟩]
theorem checked25761 : checkPrefixCuts (2^48) 3380477953 9 Manual.Count131072.C025761.packed 128 cuts25761 = true := by
 decide +kernel
def pointBounds25761 : List (Nat × Nat × Nat) := [(3380574208,103282817918346,103283200150459)]
theorem point_links_checked25761 : (cuts25761.take 1).map (fun c => (3380477953-1+2*2^9*c.k,103282455471734+c.lower,103282837703640+c.upper)) = pointBounds25761 := by
 decide +kernel
def cuts25762 : List PrefixCut := [⟨70,270680590,270680740⟩,
⟨128,499143536,499143811⟩]
theorem checked25762 : checkPrefixCuts (2^48) 3380609025 9 Manual.Count131072.C025762.packed 128 cuts25762 = true := by
 decide +kernel
def pointBounds25762 : List (Nat × Nat × Nat) := [(3380680704,103283221568387,103283603800725)]
theorem point_links_checked25762 : (cuts25762.take 1).map (fun c => (3380609025-1+2*2^9*c.k,103282950887797+c.lower,103283333119985+c.upper)) = pointBounds25762 := by
 decide +kernel
def cuts25763 : List PrefixCut := [⟨46,180752632,180752732⟩,
⟨128,492880041,492880314⟩]
theorem checked25763 : checkPrefixCuts (2^48) 3380740097 9 Manual.Count131072.C025763.packed 128 cuts25763 = true := by
 decide +kernel
def pointBounds25763 : List (Nat × Nat × Nat) := [(3380787200,103283630783965,103284013016528)]
theorem point_links_checked25763 : (cuts25763.take 1).map (fun c => (3380740097-1+2*2^9*c.k,103283450031333+c.lower,103283832263796+c.upper)) = pointBounds25763 := by
 decide +kernel
def cuts25764 : List PrefixCut := [⟨22,85086463,85086510⟩,
⟨126,493943318,493943596⟩,
⟨128,501769000,501769283⟩]
theorem checked25764 : checkPrefixCuts (2^48) 3380871169 9 Manual.Count131072.C025764.packed 128 cuts25764 = true := by
 decide +kernel
def pointBounds25764 : List (Nat × Nat × Nat) := [(3380893696,103284027997837,103284410230620),(3381000192,103284436854692,103284819087706)]
theorem point_links_checked25764 : (cuts25764.take 2).map (fun c => (3380871169-1+2*2^9*c.k,103283942911374+c.lower,103284325144110+c.upper)) = pointBounds25764 := by
 decide +kernel
def cuts25765 : List PrefixCut := [⟨102,394524724,394524946⟩,
⟨128,498835739,498836017⟩]
theorem checked25765 : checkPrefixCuts (2^48) 3381002241 9 Manual.Count131072.C025765.packed 128 cuts25765 = true := by
 decide +kernel
def pointBounds25765 : List (Nat × Nat × Nat) := [(3381106688,103284839205098,103285221438339)]
theorem point_links_checked25765 : (cuts25765.take 1).map (fun c => (3381002241-1+2*2^9*c.k,103284444680374+c.lower,103284826913393+c.upper)) = pointBounds25765 := by
 decide +kernel
def cuts25766 : List PrefixCut := [⟨78,299192204,299192370⟩,
⟨128,492739346,492739623⟩]
theorem checked25766 : checkPrefixCuts (2^48) 3381133313 9 Manual.Count131072.C025766.packed 128 cuts25766 = true := by
 decide +kernel
def pointBounds25766 : List (Nat × Nat × Nat) := [(3381213184,103285242708317,103285624941780)]
theorem point_links_checked25766 : (cuts25766.take 1).map (fun c => (3381133313-1+2*2^9*c.k,103284943516113+c.lower,103285325749410+c.upper)) = pointBounds25766 := by
 decide +kernel
def cuts25767 : List PrefixCut := [⟨54,206613546,206613663⟩,
⟨128,496882441,496882721⟩]
theorem checked25767 : checkPrefixCuts (2^48) 3381264385 9 Manual.Count131072.C025767.packed 128 cuts25767 = true := by
 decide +kernel
def pointBounds25767 : List (Nat × Nat × Nat) := [(3381319680,103285642869005,103286025102696)]
theorem point_links_checked25767 : (cuts25767.take 1).map (fun c => (3381264385-1+2*2^9*c.k,103285436255459+c.lower,103285818489033+c.upper)) = pointBounds25767 := by
 decide +kernel
def cuts25768 : List PrefixCut := [⟨30,114707274,114707340⟩,
⟨128,499360437,499360718⟩]
theorem checked25768 : checkPrefixCuts (2^48) 3381395457 9 Manual.Count131072.C025768.packed 128 cuts25768 = true := by
 decide +kernel
def pointBounds25768 : List (Nat × Nat × Nat) := [(3381426176,103286047845174,103286430079094)]
theorem point_links_checked25768 : (cuts25768.take 1).map (fun c => (3381395457-1+2*2^9*c.k,103285933137900+c.lower,103286315371754+c.upper)) = pointBounds25768 := by
 decide +kernel
def cuts25769 : List PrefixCut := [⟨6,22973946,22973958⟩,
⟨110,428424007,428424244⟩,
⟨128,497509891,497510165⟩]
theorem checked25769 : checkPrefixCuts (2^48) 3381526529 9 Manual.Count131072.C025769.packed 128 cuts25769 = true := by
 decide +kernel
def pointBounds25769 : List (Nat × Nat × Nat) := [(3381532672,103286455472283,103286837706430),(3381639168,103286860922344,103287243156716)]
theorem point_links_checked25769 : (cuts25769.take 2).map (fun c => (3381526529-1+2*2^9*c.k,103286432498337+c.lower,103286814732472+c.upper)) = pointBounds25769 := by
 decide +kernel
def cuts25770 : List PrefixCut := [⟨86,328777047,328777235⟩,
⟨128,490831845,490832128⟩]
theorem checked25770 : checkPrefixCuts (2^48) 3381657601 9 Manual.Count131072.C025770.packed 128 cuts25770 = true := by
 decide +kernel
def pointBounds25770 : List (Nat × Nat × Nat) := [(3381745664,103287258785275,103287641019872)]
theorem point_links_checked25770 : (cuts25770.take 1).map (fun c => (3381657601-1+2*2^9*c.k,103286930008228+c.lower,103287312242637+c.upper)) = pointBounds25770 := by
 decide +kernel
def cuts25771 : List PrefixCut := [⟨62,236211774,236211908⟩,
⟨128,492227781,492228053⟩]
theorem checked25771 : checkPrefixCuts (2^48) 3381788673 9 Manual.Count131072.C025771.packed 128 cuts25771 = true := by
 decide +kernel
def pointBounds25771 : List (Nat × Nat × Nat) := [(3381852160,103287657051847,103288039286673)]
theorem point_links_checked25771 : (cuts25771.take 1).map (fun c => (3381788673-1+2*2^9*c.k,103287420840073+c.lower,103287803074765+c.upper)) = pointBounds25771 := by
 decide +kernel
def cuts25772 : List PrefixCut := [⟨38,146649227,146649315⟩,
⟨128,494372619,494372909⟩]
theorem checked25772 : checkPrefixCuts (2^48) 3381919745 9 Manual.Count131072.C025772.packed 128 cuts25772 = true := by
 decide +kernel
def pointBounds25772 : List (Nat × Nat × Nat) := [(3381958656,103288059717081,103288441952133)]
theorem point_links_checked25772 : (cuts25772.take 1).map (fun c => (3381919745-1+2*2^9*c.k,103287913067854+c.lower,103288295302818+c.upper)) = pointBounds25772 := by
 decide +kernel
def cuts25773 : List PrefixCut := [⟨14,53597496,53597526⟩,
⟨118,458650825,458651089⟩,
⟨128,495851504,495851789⟩]
theorem checked25773 : checkPrefixCuts (2^48) 3382050817 9 Manual.Count131072.C025773.packed 128 cuts25773 = true := by
 decide +kernel
def pointBounds25773 : List (Nat × Nat × Nat) := [(3382065152,103288461037969,103288843273253),(3382171648,103288866091298,103289248326816)]
theorem point_links_checked25773 : (cuts25773.take 2).map (fun c => (3382050817-1+2*2^9*c.k,103288407440473+c.lower,103288789675727+c.upper)) = pointBounds25773 := by
 decide +kernel
def cuts25774 : List PrefixCut := [⟨94,368422438,368422643⟩,
⟨128,500409478,500409756⟩]
theorem checked25774 : checkPrefixCuts (2^48) 3382181889 9 Manual.Count131072.C025774.packed 128 cuts25774 = true := by
 decide +kernel
def pointBounds25774 : List (Nat × Nat × Nat) := [(3382278144,103289271714415,103289653950159)]
theorem point_links_checked25774 : (cuts25774.take 1).map (fun c => (3382181889-1+2*2^9*c.k,103288903291977+c.lower,103289285527516+c.upper)) = pointBounds25774 := by
 decide +kernel
def cuts25775 : List PrefixCut := [⟨70,266632927,266633079⟩,
⟨128,493066825,493067104⟩]
theorem checked25775 : checkPrefixCuts (2^48) 3382312961 9 Manual.Count131072.C025775.packed 128 cuts25775 = true := by
 decide +kernel
def pointBounds25775 : List (Nat × Nat × Nat) := [(3382384640,103289670334382,103290052570351)]
theorem point_links_checked25775 : (cuts25775.take 1).map (fun c => (3382312961-1+2*2^9*c.k,103289403701455+c.lower,103289785937272+c.upper)) = pointBounds25775 := by
 decide +kernel
def cuts25776 : List PrefixCut := [⟨46,178830857,178830958⟩,
⟨128,494712103,494712381⟩]
theorem checked25776 : checkPrefixCuts (2^48) 3382444033 9 Manual.Count131072.C025776.packed 128 cuts25776 = true := by
 decide +kernel
def pointBounds25776 : List (Nat × Nat × Nat) := [(3382491136,103290075599137,103290457835334)]
theorem point_links_checked25776 : (cuts25776.take 1).map (fun c => (3382444033-1+2*2^9*c.k,103289896768280+c.lower,103290279004376+c.upper)) = pointBounds25776 := by
 decide +kernel
def cuts25777 : List PrefixCut := [⟨22,86624654,86624702⟩,
⟨126,483792382,483792655⟩,
⟨128,491697332,491697610⟩]
theorem checked25777 : checkPrefixCuts (2^48) 3382575105 9 Manual.Count131072.C025777.packed 128 cuts25777 = true := by
 decide +kernel
def pointBounds25777 : List (Nat × Nat × Nat) := [(3382597632,103290478105037,103290860341459),(3382704128,103290875272765,103291257509412)]
theorem point_links_checked25777 : (cuts25777.take 2).map (fun c => (3382575105-1+2*2^9*c.k,103290391480383+c.lower,103290773716757+c.upper)) = pointBounds25777 := by
 decide +kernel
def cuts25778 : List PrefixCut := [⟨102,400733047,400733268⟩,
⟨128,503909824,503910103⟩]
theorem checked25778 : checkPrefixCuts (2^48) 3382706177 9 Manual.Count131072.C025778.packed 128 cuts25778 = true := by
 decide +kernel
def pointBounds25778 : List (Nat × Nat × Nat) := [(3382810624,103291283910762,103291666147635)]
theorem point_links_checked25778 : (cuts25778.take 1).map (fun c => (3382706177-1+2*2^9*c.k,103290883177715+c.lower,103291265414367+c.upper)) = pointBounds25778 := by
 decide +kernel
def cuts25779 : List PrefixCut := [⟨78,300539244,300539410⟩,
⟨128,497733087,497733357⟩]
theorem checked25779 : checkPrefixCuts (2^48) 3382837249 9 Manual.Count131072.C025779.packed 128 cuts25779 = true := by
 decide +kernel
def pointBounds25779 : List (Nat × Nat × Nat) := [(3382917120,103291687626783,103292069863880)]
theorem point_links_checked25779 : (cuts25779.take 1).map (fun c => (3382837249-1+2*2^9*c.k,103291387087539+c.lower,103291769324470+c.upper)) = pointBounds25779 := by
 decide +kernel
def cuts25780 : List PrefixCut := [⟨54,211584857,211584973⟩,
⟨128,501624357,501624638⟩]
theorem checked25780 : checkPrefixCuts (2^48) 3382968321 9 Manual.Count131072.C025780.packed 128 cuts25780 = true := by
 decide +kernel
def pointBounds25780 : List (Nat × Nat × Nat) := [(3383023616,103292096405483,103292478642800)]
theorem point_links_checked25780 : (cuts25780.take 1).map (fun c => (3382968321-1+2*2^9*c.k,103291884820626+c.lower,103292267057827+c.upper)) = pointBounds25780 := by
 decide +kernel
def cuts25781 : List PrefixCut := [⟨30,117894288,117894354⟩,
⟨128,501188877,501189150⟩]
theorem checked25781 : checkPrefixCuts (2^48) 3383099393 9 Manual.Count131072.C025781.packed 128 cuts25781 = true := by
 decide +kernel
def pointBounds25781 : List (Nat × Nat × Nat) := [(3383130112,103292504339271,103292886576819)]
theorem point_links_checked25781 : (cuts25781.take 1).map (fun c => (3383099393-1+2*2^9*c.k,103292386444983+c.lower,103292768682465+c.upper)) = pointBounds25781 := by
 decide +kernel
def cuts25782 : List PrefixCut := [⟨6,21964011,21964022⟩,
⟨110,424131633,424131865⟩,
⟨128,492766758,492767028⟩]
theorem checked25782 : checkPrefixCuts (2^48) 3383230465 9 Manual.Count131072.C025782.packed 128 cuts25782 = true := by
 decide +kernel
def pointBounds25782 : List (Nat × Nat × Nat) := [(3383236608,103292909597871,103293291835637),(3383343104,103293311765493,103293694003480)]
theorem point_links_checked25782 : (cuts25782.take 2).map (fun c => (3383230465-1+2*2^9*c.k,103292887633860+c.lower,103293269871615+c.upper)) = pointBounds25782 := by
 decide +kernel
def cuts25783 : List PrefixCut := [⟨86,333270235,333270423⟩,
⟨128,491250244,491250523⟩]
theorem checked25783 : checkPrefixCuts (2^48) 3383361537 9 Manual.Count131072.C025783.packed 128 cuts25783 = true := by
 decide +kernel
def pointBounds25783 : List (Nat × Nat × Nat) := [(3383449600,103293713670853,103294095909066)]
theorem point_links_checked25783 : (cuts25783.take 1).map (fun c => (3383361537-1+2*2^9*c.k,103293380400618+c.lower,103293762638643+c.upper)) = pointBounds25783 := by
 decide +kernel
def cuts25784 : List PrefixCut := [⟨62,241167388,241167520⟩,
⟨128,499383698,499383974⟩]
theorem checked25784 : checkPrefixCuts (2^48) 3383492609 9 Manual.Count131072.C025784.packed 128 cuts25784 = true := by
 decide +kernel
def pointBounds25784 : List (Nat × Nat × Nat) := [(3383556096,103294112818250,103294495056686)]
theorem point_links_checked25784 : (cuts25784.take 1).map (fun c => (3383492609-1+2*2^9*c.k,103293871650862+c.lower,103294253889166+c.upper)) = pointBounds25784 := by
 decide +kernel
def cuts25785 : List PrefixCut := [⟨38,148821404,148821489⟩,
⟨128,497950186,497950467⟩]
theorem checked25785 : checkPrefixCuts (2^48) 3383623681 9 Manual.Count131072.C025785.packed 128 cuts25785 = true := by
 decide +kernel
def pointBounds25785 : List (Nat × Nat × Nat) := [(3383662592,103294519855964,103294902094629)]
theorem point_links_checked25785 : (cuts25785.take 1).map (fun c => (3383623681-1+2*2^9*c.k,103294371034560+c.lower,103294753273140+c.upper)) = pointBounds25785 := by
 decide +kernel
def cuts25786 : List PrefixCut := [⟨14,57480151,57480183⟩,
⟨118,458503132,458503387⟩,
⟨128,497182341,497182618⟩]
theorem checked25786 : checkPrefixCuts (2^48) 3383754753 9 Manual.Count131072.C025786.packed 128 cuts25786 = true := by
 decide +kernel
def pointBounds25786 : List (Nat × Nat × Nat) := [(3383769088,103294926464897,103295308703790),(3383875584,103295327487878,103295709726994)]
theorem point_links_checked25786 : (cuts25786.take 2).map (fun c => (3383754753-1+2*2^9*c.k,103294868984746+c.lower,103295251223607+c.upper)) = pointBounds25786 := by
 decide +kernel
def cuts25787 : List PrefixCut := [⟨94,362913421,362913618⟩,
⟨128,496081673,496081945⟩]
theorem checked25787 : checkPrefixCuts (2^48) 3383885825 9 Manual.Count131072.C025787.packed 128 cuts25787 = true := by
 decide +kernel
def pointBounds25787 : List (Nat × Nat × Nat) := [(3383982080,103295729080508,103296111319843)]
theorem point_links_checked25787 : (cuts25787.take 1).map (fun c => (3383885825-1+2*2^9*c.k,103295366167087+c.lower,103295748406225+c.upper)) = pointBounds25787 := by
 decide +kernel
def cuts25788 : List PrefixCut := [⟨70,275814422,275814571⟩,
⟨128,502882850,502883124⟩]
theorem checked25788 : checkPrefixCuts (2^48) 3384016897 9 Manual.Count131072.C025788.packed 128 cuts25788 = true := by
 decide +kernel
def pointBounds25788 : List (Nat × Nat × Nat) := [(3384088576,103296138063182,103296520302741)]
theorem point_links_checked25788 : (cuts25788.take 1).map (fun c => (3384016897-1+2*2^9*c.k,103295862248760+c.lower,103296244488170+c.upper)) = pointBounds25788 := by
 decide +kernel
def cuts25789 : List PrefixCut := [⟨46,180903359,180903462⟩,
⟨128,498538523,498538808⟩]
theorem checked25789 : checkPrefixCuts (2^48) 3384147969 9 Manual.Count131072.C025789.packed 128 cuts25789 = true := by
 decide +kernel
def pointBounds25789 : List (Nat × Nat × Nat) := [(3384195072,103296546034969,103296928274756)]
theorem point_links_checked25789 : (cuts25789.take 1).map (fun c => (3384147969-1+2*2^9*c.k,103296365131610+c.lower,103296747371294+c.upper)) = pointBounds25789 := by
 decide +kernel
def cuts25790 : List PrefixCut := [⟨22,86082006,86082053⟩,
⟨126,490202324,490202596⟩,
⟨128,496606268,496606544⟩]
theorem checked25790 : checkPrefixCuts (2^48) 3384279041 9 Manual.Count131072.C025790.packed 128 cuts25790 = true := by
 decide +kernel
def pointBounds25790 : List (Nat × Nat × Nat) := [(3384301568,103296949752139,103297331992155),(3384408064,103297353872457,103297736112698)]
theorem point_links_checked25790 : (cuts25790.take 2).map (fun c => (3384279041-1+2*2^9*c.k,103296863670133+c.lower,103297245910102+c.upper)) = pointBounds25790 := by
 decide +kernel
def cuts25791 : List PrefixCut := [⟨102,397204618,397204838⟩,
⟨128,496171198,496171472⟩]
theorem checked25791 : checkPrefixCuts (2^48) 3384410113 9 Manual.Count131072.C025791.packed 128 cuts25791 = true := by
 decide +kernel
def pointBounds25791 : List (Nat × Nat × Nat) := [(3384514560,103297757481019,103298139721484)]
theorem point_links_checked25791 : (cuts25791.take 1).map (fun c => (3384410113-1+2*2^9*c.k,103297360276401+c.lower,103297742516646+c.upper)) = pointBounds25791 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000180
