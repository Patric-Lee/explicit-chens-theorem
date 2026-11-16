import PlattAssemblyKernel
import PlattCertificates.Count131072.C025824
import PlattCertificates.Count131072.C025825
import PlattCertificates.Count131072.C025826
import PlattCertificates.Count131072.C025827
import PlattCertificates.Count131072.C025828
import PlattCertificates.Count131072.C025829
import PlattCertificates.Count131072.C025830
import PlattCertificates.Count131072.C025831
import PlattCertificates.Count131072.C025832
import PlattCertificates.Count131072.C025833
import PlattCertificates.Count131072.C025834
import PlattCertificates.Count131072.C025835
import PlattCertificates.Count131072.C025836
import PlattCertificates.Count131072.C025837
import PlattCertificates.Count131072.C025838
import PlattCertificates.Count131072.C025839
import PlattCertificates.Count131072.C025840
import PlattCertificates.Count131072.C025841
import PlattCertificates.Count131072.C025842
import PlattCertificates.Count131072.C025843
import PlattCertificates.Count131072.C025844
import PlattCertificates.Count131072.C025845
import PlattCertificates.Count131072.C025846
import PlattCertificates.Count131072.C025847
import PlattCertificates.Count131072.C025848
import PlattCertificates.Count131072.C025849
import PlattCertificates.Count131072.C025850
import PlattCertificates.Count131072.C025851
import PlattCertificates.Count131072.C025852
import PlattCertificates.Count131072.C025853
import PlattCertificates.Count131072.C025854
import PlattCertificates.Count131072.C025855
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000182
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts25824 : List PrefixCut := [⟨38,149510616,149510699⟩,
⟨128,501850473,501850753⟩]
theorem checked25824 : checkPrefixCuts (2^48) 3388735489 9 Manual.Count131072.C025824.packed 128 cuts25824 = true := by
 decide +kernel
def pointBounds25824 : List (Nat × Nat × Nat) := [(3388774400,103313899646125,103314281895680)]
theorem point_links_checked25824 : (cuts25824.take 1).map (fun c => (3388735489-1+2*2^9*c.k,103313750135509+c.lower,103314132384981+c.upper)) = pointBounds25824 := by
 decide +kernel
def cuts25825 : List PrefixCut := [⟨14,55898394,55898425⟩,
⟨118,454240020,454240275⟩,
⟨128,493940611,493940889⟩]
theorem checked25825 : checkPrefixCuts (2^48) 3388866561 9 Manual.Count131072.C025825.packed 128 cuts25825 = true := by
 decide +kernel
def pointBounds25825 : List (Nat × Nat × Nat) := [(3388880896,103314307884376,103314690134159),(3388987392,103314706226002,103315088476009)]
theorem point_links_checked25825 : (cuts25825.take 2).map (fun c => (3388866561-1+2*2^9*c.k,103314251985982+c.lower,103314634235734+c.upper)) = pointBounds25825 := by
 decide +kernel
def cuts25826 : List PrefixCut := [⟨94,364940722,364940923⟩,
⟨128,492177479,492177752⟩]
theorem checked25826 : checkPrefixCuts (2^48) 3388997633 9 Manual.Count131072.C025826.packed 128 cuts25826 = true := by
 decide +kernel
def pointBounds25826 : List (Nat × Nat × Nat) := [(3389093888,103315110867315,103315493117546)]
theorem point_links_checked25826 : (cuts25826.take 1).map (fun c => (3388997633-1+2*2^9*c.k,103314745926593+c.lower,103315128176623+c.upper)) = pointBounds25826 := by
 decide +kernel
def cuts25827 : List PrefixCut := [⟨70,272989953,272990110⟩,
⟨128,500297275,500297557⟩]
theorem checked25827 : checkPrefixCuts (2^48) 3389128705 9 Manual.Count131072.C025827.packed 128 cuts25827 = true := by
 decide +kernel
def pointBounds25827 : List (Nat × Nat × Nat) := [(3389200384,103315511094025,103315893344485)]
theorem point_links_checked25827 : (cuts25827.take 1).map (fun c => (3389128705-1+2*2^9*c.k,103315238104072+c.lower,103315620354375+c.upper)) = pointBounds25827 := by
 decide +kernel
def cuts25828 : List PrefixCut := [⟨46,176062811,176062909⟩,
⟨128,497371199,497371474⟩]
theorem checked25828 : checkPrefixCuts (2^48) 3389259777 9 Manual.Count131072.C025828.packed 128 cuts25828 = true := by
 decide +kernel
def pointBounds25828 : List (Nat × Nat × Nat) := [(3389306880,103315914464158,103316296714841)]
theorem point_links_checked25828 : (cuts25828.take 1).map (fun c => (3389259777-1+2*2^9*c.k,103315738401347+c.lower,103316120651932+c.upper)) = pointBounds25828 := by
 decide +kernel
def cuts25829 : List PrefixCut := [⟨22,84706502,84706548⟩,
⟨126,488217384,488217661⟩,
⟨128,496438610,496438891⟩]
theorem checked25829 : checkPrefixCuts (2^48) 3389390849 9 Manual.Count131072.C025829.packed 128 cuts25829 = true := by
 decide +kernel
def pointBounds25829 : List (Nat × Nat × Nat) := [(3389413376,103316320479048,103316702729954),(3389519872,103316723989930,103317106241067)]
theorem point_links_checked25829 : (cuts25829.take 2).map (fun c => (3389390849-1+2*2^9*c.k,103316235772546+c.lower,103316618023406+c.upper)) = pointBounds25829 := by
 decide +kernel
def cuts25830 : List PrefixCut := [⟨102,400757691,400757912⟩,
⟨128,503062683,503062960⟩]
theorem checked25830 : checkPrefixCuts (2^48) 3389521921 9 Manual.Count131072.C025830.packed 128 cuts25830 = true := by
 decide +kernel
def pointBounds25830 : List (Nat × Nat × Nat) := [(3389626368,103317132968847,103317515220209)]
theorem point_links_checked25830 : (cuts25830.take 1).map (fun c => (3389521921-1+2*2^9*c.k,103316732211156+c.lower,103317114462297+c.upper)) = pointBounds25830 := by
 decide +kernel
def cuts25831 : List PrefixCut := [⟨78,305996738,305996903⟩,
⟨128,500469061,500469336⟩]
theorem checked25831 : checkPrefixCuts (2^48) 3389652993 9 Manual.Count131072.C025831.packed 128 cuts25831 = true := by
 decide +kernel
def pointBounds25831 : List (Nat × Nat × Nat) := [(3389732864,103317541270577,103317923522160)]
theorem point_links_checked25831 : (cuts25831.take 1).map (fun c => (3389652993-1+2*2^9*c.k,103317235273839+c.lower,103317617525257+c.upper)) = pointBounds25831 := by
 decide +kernel
def cuts25832 : List PrefixCut := [⟨54,205346935,205347050⟩,
⟨128,492810491,492810762⟩]
theorem checked25832 : checkPrefixCuts (2^48) 3389784065 9 Manual.Count131072.C025832.packed 128 cuts25832 = true := by
 decide +kernel
def pointBounds25832 : List (Nat × Nat × Nat) := [(3389839360,103317941089835,103318323341643)]
theorem point_links_checked25832 : (cuts25832.take 1).map (fun c => (3389784065-1+2*2^9*c.k,103317735742900+c.lower,103318117994593+c.upper)) = pointBounds25832 := by
 decide +kernel
def cuts25833 : List PrefixCut := [⟨30,119068815,119068877⟩,
⟨128,496777023,496777295⟩]
theorem checked25833 : checkPrefixCuts (2^48) 3389915137 9 Manual.Count131072.C025833.packed 128 cuts25833 = true := by
 decide +kernel
def pointBounds25833 : List (Nat × Nat × Nat) := [(3389945856,103318347622206,103318729874232)]
theorem point_links_checked25833 : (cuts25833.take 1).map (fun c => (3389915137-1+2*2^9*c.k,103318228553391+c.lower,103318610805355+c.upper)) = pointBounds25833 := by
 decide +kernel
def cuts25834 : List PrefixCut := [⟨6,23580445,23580458⟩,
⟨110,428675813,428676059⟩,
⟨128,501158234,501158520⟩]
theorem checked25834 : checkPrefixCuts (2^48) 3390046209 9 Manual.Count131072.C025834.packed 128 cuts25834 = true := by
 decide +kernel
def pointBounds25834 : List (Nat × Nat × Nat) := [(3390052352,103318748910859,103319131163108),(3390158848,103319154006227,103319536258709)]
theorem point_links_checked25834 : (cuts25834.take 2).map (fun c => (3390046209-1+2*2^9*c.k,103318725330414+c.lower,103319107582650+c.upper)) = pointBounds25834 := by
 decide +kernel
def cuts25835 : List PrefixCut := [⟨86,330939720,330939904⟩,
⟨128,495659160,495659436⟩]
theorem checked25835 : checkPrefixCuts (2^48) 3390177281 9 Manual.Count131072.C025835.packed 128 cuts25835 = true := by
 decide +kernel
def pointBounds25835 : List (Nat × Nat × Nat) := [(3390265344,103319557428368,103319939681074)]
theorem point_links_checked25835 : (cuts25835.take 1).map (fun c => (3390177281-1+2*2^9*c.k,103319226488648+c.lower,103319608741170+c.upper)) = pointBounds25835 := by
 decide +kernel
def cuts25836 : List PrefixCut := [⟨62,244750676,244750815⟩,
⟨128,503195067,503195353⟩]
theorem checked25836 : checkPrefixCuts (2^48) 3390308353 9 Manual.Count131072.C025836.packed 128 cuts25836 = true := by
 decide +kernel
def pointBounds25836 : List (Nat × Nat × Nat) := [(3390371840,103319966898484,103320349151421)]
theorem point_links_checked25836 : (cuts25836.take 1).map (fun c => (3390308353-1+2*2^9*c.k,103319722147808+c.lower,103320104400606+c.upper)) = pointBounds25836 := by
 decide +kernel
def cuts25837 : List PrefixCut := [⟨38,144620327,144620409⟩,
⟨128,494873651,494873932⟩]
theorem checked25837 : checkPrefixCuts (2^48) 3390439425 9 Manual.Count131072.C025837.packed 128 cuts25837 = true := by
 decide +kernel
def pointBounds25837 : List (Nat × Nat × Nat) := [(3390478336,103320369963202,103320752216368)]
theorem point_links_checked25837 : (cuts25837.take 1).map (fun c => (3390439425-1+2*2^9*c.k,103320225342875+c.lower,103320607595959+c.upper)) = pointBounds25837 := by
 decide +kernel
def cuts25838 : List PrefixCut := [⟨14,53047733,53047761⟩,
⟨118,458660596,458660843⟩,
⟨128,497594109,497594378⟩]
theorem checked25838 : checkPrefixCuts (2^48) 3390570497 9 Manual.Count131072.C025838.packed 128 cuts25838 = true := by
 decide +kernel
def pointBounds25838 : List (Nat × Nat × Nat) := [(3390584832,103320773264259,103321155517652),(3390691328,103321178877122,103321561130734)]
theorem point_links_checked25838 : (cuts25838.take 2).map (fun c => (3390570497-1+2*2^9*c.k,103320720216526+c.lower,103321102469891+c.upper)) = pointBounds25838 := by
 decide +kernel
def cuts25839 : List PrefixCut := [⟨94,368409880,368410083⟩,
⟨128,497491940,497492219⟩]
theorem checked25839 : checkPrefixCuts (2^48) 3390701569 9 Manual.Count131072.C025839.packed 128 cuts25839 = true := by
 decide +kernel
def pointBounds25839 : List (Nat × Nat × Nat) := [(3390797824,103321586220515,103321968474352)]
theorem point_links_checked25839 : (cuts25839.take 1).map (fun c => (3390701569-1+2*2^9*c.k,103321217810635+c.lower,103321600064269+c.upper)) = pointBounds25839 := by
 decide +kernel
def cuts25840 : List PrefixCut := [⟨70,272603782,272603934⟩,
⟨128,497887717,497887996⟩]
theorem checked25840 : checkPrefixCuts (2^48) 3390832641 9 Manual.Count131072.C025840.packed 128 cuts25840 = true := by
 decide +kernel
def pointBounds25840 : List (Nat × Nat × Nat) := [(3390904320,103321987906357,103322370160422)]
theorem point_links_checked25840 : (cuts25840.take 1).map (fun c => (3390832641-1+2*2^9*c.k,103321715302575+c.lower,103322097556488+c.upper)) = pointBounds25840 := by
 decide +kernel
def cuts25841 : List PrefixCut := [⟨46,177385483,177385584⟩,
⟨128,495212254,495212527⟩]
theorem checked25841 : checkPrefixCuts (2^48) 3390963713 9 Manual.Count131072.C025841.packed 128 cuts25841 = true := by
 decide +kernel
def pointBounds25841 : List (Nat × Nat × Nat) := [(3391010816,103322390575775,103322772830068)]
theorem point_links_checked25841 : (cuts25841.take 1).map (fun c => (3390963713-1+2*2^9*c.k,103322213190292+c.lower,103322595444484+c.upper)) = pointBounds25841 := by
 decide +kernel
def cuts25842 : List PrefixCut := [⟨22,85576983,85577029⟩,
⟨126,482410897,482411165⟩,
⟨128,490544990,490545263⟩]
theorem checked25842 : checkPrefixCuts (2^48) 3391094785 9 Manual.Count131072.C025842.packed 128 cuts25842 = true := by
 decide +kernel
def pointBounds25842 : List (Nat × Nat × Nat) := [(3391117312,103322793979529,103323176234040),(3391223808,103323190813443,103323573068176)]
theorem point_links_checked25842 : (cuts25842.take 2).map (fun c => (3391094785-1+2*2^9*c.k,103322708402546+c.lower,103323090657011+c.upper)) = pointBounds25842 := by
 decide +kernel
def cuts25843 : List PrefixCut := [⟨102,391343424,391343636⟩,
⟨128,493265025,493265295⟩]
theorem checked25843 : checkPrefixCuts (2^48) 3391225857 9 Manual.Count131072.C025843.packed 128 cuts25843 = true := by
 decide +kernel
def pointBounds25843 : List (Nat × Nat × Nat) := [(3391330304,103323590290960,103323972545910)]
theorem point_links_checked25843 : (cuts25843.take 1).map (fun c => (3391225857-1+2*2^9*c.k,103323198947536+c.lower,103323581202274+c.upper)) = pointBounds25843 := by
 decide +kernel
def cuts25844 : List PrefixCut := [⟨78,297377305,297377472⟩,
⟨128,487187186,487187462⟩]
theorem checked25844 : checkPrefixCuts (2^48) 3391356929 9 Manual.Count131072.C025844.packed 128 cuts25844 = true := by
 decide +kernel
def pointBounds25844 : List (Nat × Nat × Nat) := [(3391436800,103323989589866,103324371845041)]
theorem point_links_checked25844 : (cuts25844.take 1).map (fun c => (3391356929-1+2*2^9*c.k,103323692212561+c.lower,103324074467569+c.upper)) = pointBounds25844 := by
 decide +kernel
def cuts25845 : List PrefixCut := [⟨54,207484588,207484704⟩,
⟨128,494803705,494803982⟩]
theorem checked25845 : checkPrefixCuts (2^48) 3391488001 9 Manual.Count131072.C025845.packed 128 cuts25845 = true := by
 decide +kernel
def pointBounds25845 : List (Nat × Nat × Nat) := [(3391543296,103324386884335,103324769139735)]
theorem point_links_checked25845 : (cuts25845.take 1).map (fun c => (3391488001-1+2*2^9*c.k,103324179399747+c.lower,103324561655031+c.upper)) = pointBounds25845 := by
 decide +kernel
def cuts25846 : List PrefixCut := [⟨30,112120747,112120809⟩,
⟨128,491381960,491382235⟩]
theorem checked25846 : checkPrefixCuts (2^48) 3391619073 9 Manual.Count131072.C025846.packed 128 cuts25846 = true := by
 decide +kernel
def pointBounds25846 : List (Nat × Nat × Nat) := [(3391649792,103324786324199,103325168579822)]
theorem point_links_checked25846 : (cuts25846.take 1).map (fun c => (3391619073-1+2*2^9*c.k,103324674203452+c.lower,103325056459013+c.upper)) = pointBounds25846 := by
 decide +kernel
def cuts25847 : List PrefixCut := [⟨6,23485610,23485622⟩,
⟨110,418336032,418336267⟩,
⟨128,489620252,489620526⟩]
theorem checked25847 : checkPrefixCuts (2^48) 3391750145 9 Manual.Count131072.C025847.packed 128 cuts25847 = true := by
 decide +kernel
def pointBounds25847 : List (Nat × Nat × Nat) := [(3391756288,103325189071022,103325571326870),(3391862784,103325583921444,103325966177515)]
theorem point_links_checked25847 : (cuts25847.take 2).map (fun c => (3391750145-1+2*2^9*c.k,103325165585412+c.lower,103325547841248+c.upper)) = pointBounds25847 := by
 decide +kernel
def cuts25848 : List PrefixCut := [⟨86,326209359,326209542⟩,
⟨128,484871345,484871615⟩]
theorem checked25848 : checkPrefixCuts (2^48) 3391881217 9 Manual.Count131072.C025848.packed 128 cuts25848 = true := by
 decide +kernel
def pointBounds25848 : List (Nat × Nat × Nat) := [(3391969280,103325981415023,103326363671316)]
theorem point_links_checked25848 : (cuts25848.take 1).map (fun c => (3391881217-1+2*2^9*c.k,103325655205664+c.lower,103326037461774+c.upper)) = pointBounds25848 := by
 decide +kernel
def cuts25849 : List PrefixCut := [⟨62,240312700,240312835⟩,
⟨128,498212409,498212685⟩]
theorem checked25849 : checkPrefixCuts (2^48) 3392012289 9 Manual.Count131072.C025849.packed 128 cuts25849 = true := by
 decide +kernel
def pointBounds25849 : List (Nat × Nat × Nat) := [(3392075776,103326380389709,103326762646224)]
theorem point_links_checked25849 : (cuts25849.take 1).map (fun c => (3392012289-1+2*2^9*c.k,103326140077009+c.lower,103326522333389+c.upper)) = pointBounds25849 := by
 decide +kernel
def cuts25850 : List PrefixCut := [⟨38,144215768,144215849⟩,
⟨128,493961316,493961601⟩]
theorem checked25850 : checkPrefixCuts (2^48) 3392143361 9 Manual.Count131072.C025850.packed 128 cuts25850 = true := by
 decide +kernel
def pointBounds25850 : List (Nat × Nat × Nat) := [(3392182272,103326782505186,103327164761923)]
theorem point_links_checked25850 : (cuts25850.take 1).map (fun c => (3392143361-1+2*2^9*c.k,103326638289418+c.lower,103327020546074+c.upper)) = pointBounds25850 := by
 decide +kernel
def cuts25851 : List PrefixCut := [⟨14,55759268,55759298⟩,
⟨118,450713728,450713987⟩,
⟨128,489461740,489462020⟩]
theorem checked25851 : checkPrefixCuts (2^48) 3392274433 9 Manual.Count131072.C025851.packed 128 cuts25851 = true := by
 decide +kernel
def pointBounds25851 : List (Nat × Nat × Nat) := [(3392288768,103327188010002,103327570266973),(3392395264,103327582964462,103327965221662)]
theorem point_links_checked25851 : (cuts25851.take 2).map (fun c => (3392274433-1+2*2^9*c.k,103327132250734+c.lower,103327514507675+c.upper)) = pointBounds25851 := by
 decide +kernel
def cuts25852 : List PrefixCut := [⟨94,368473776,368473973⟩,
⟨128,500726823,500727093⟩]
theorem checked25852 : checkPrefixCuts (2^48) 3392405505 9 Manual.Count131072.C025852.packed 128 cuts25852 = true := by
 decide +kernel
def pointBounds25852 : List (Nat × Nat × Nat) := [(3392501760,103327990186250,103328372443668)]
theorem point_links_checked25852 : (cuts25852.take 1).map (fun c => (3392405505-1+2*2^9*c.k,103327621712474+c.lower,103328003969695+c.upper)) = pointBounds25852 := by
 decide +kernel
def cuts25853 : List PrefixCut := [⟨70,275785577,275785731⟩,
⟨128,497139892,497140173⟩]
theorem checked25853 : checkPrefixCuts (2^48) 3392536577 9 Manual.Count131072.C025853.packed 128 cuts25853 = true := by
 decide +kernel
def pointBounds25853 : List (Nat × Nat × Nat) := [(3392608256,103328398224874,103328780482519)]
theorem point_links_checked25853 : (cuts25853.take 1).map (fun c => (3392536577-1+2*2^9*c.k,103328122439297+c.lower,103328504696788+c.upper)) = pointBounds25853 := by
 decide +kernel
def cuts25854 : List PrefixCut := [⟨46,179868285,179868390⟩,
⟨128,494465816,494466091⟩]
theorem checked25854 : checkPrefixCuts (2^48) 3392667649 9 Manual.Count131072.C025854.packed 128 cuts25854 = true := by
 decide +kernel
def pointBounds25854 : List (Nat × Nat × Nat) := [(3392714752,103328799447474,103329181705351)]
theorem point_links_checked25854 : (cuts25854.take 1).map (fun c => (3392667649-1+2*2^9*c.k,103328619579189+c.lower,103329001836961+c.upper)) = pointBounds25854 := by
 decide +kernel
def cuts25855 : List PrefixCut := [⟨22,86778437,86778485⟩,
⟨126,486648584,486648855⟩,
⟨128,494363796,494364071⟩]
theorem checked25855 : checkPrefixCuts (2^48) 3392798721 9 Manual.Count131072.C025855.packed 128 cuts25855 = true := by
 decide +kernel
def pointBounds25855 : List (Nat × Nat × Nat) := [(3392821248,103329200823442,103329583081537),(3392927744,103329600693589,103329982951907)]
theorem point_links_checked25855 : (cuts25855.take 2).map (fun c => (3392798721-1+2*2^9*c.k,103329114045005+c.lower,103329496303052+c.upper)) = pointBounds25855 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000182
