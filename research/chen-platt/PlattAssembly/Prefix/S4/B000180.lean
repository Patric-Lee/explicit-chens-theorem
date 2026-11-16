import PlattAssemblyKernel
import PlattCertificates.Count131072.C035760
import PlattCertificates.Count131072.C035761
import PlattCertificates.Count131072.C035762
import PlattCertificates.Count131072.C035763
import PlattCertificates.Count131072.C035764
import PlattCertificates.Count131072.C035765
import PlattCertificates.Count131072.C035766
import PlattCertificates.Count131072.C035767
import PlattCertificates.Count131072.C035768
import PlattCertificates.Count131072.C035769
import PlattCertificates.Count131072.C035770
import PlattCertificates.Count131072.C035771
import PlattCertificates.Count131072.C035772
import PlattCertificates.Count131072.C035773
import PlattCertificates.Count131072.C035774
import PlattCertificates.Count131072.C035775
import PlattCertificates.Count131072.C035776
import PlattCertificates.Count131072.C035777
import PlattCertificates.Count131072.C035778
import PlattCertificates.Count131072.C035779
import PlattCertificates.Count131072.C035780
import PlattCertificates.Count131072.C035781
import PlattCertificates.Count131072.C035782
import PlattCertificates.Count131072.C035783
import PlattCertificates.Count131072.C035784
import PlattCertificates.Count131072.C035785
import PlattCertificates.Count131072.C035786
import PlattCertificates.Count131072.C035787
import PlattCertificates.Count131072.C035788
import PlattCertificates.Count131072.C035789
import PlattCertificates.Count131072.C035790
import PlattCertificates.Count131072.C035791
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000180
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts35760 : List PrefixCut := [⟨16,90603185,90603241⟩,
⟨64,356108817,356109038⟩]
theorem checked35760 : checkPrefixCuts (2^48) 4691066881 10 Manual.Count131072.C035760.packed 64 cuts35760 = true := by
 decide +kernel
def pointBounds35760 : List (Nat × Nat × Nat) := [(4691099648,107454750050072,107455134701142)]
theorem point_links_checked35760 : (cuts35760.take 1).map (fun c => (4691066881-1+2*2^10*c.k,107454659446887+c.lower,107455044097901+c.upper)) = pointBounds35760 := by
 decide +kernel
def cuts35761 : List PrefixCut := [⟨24,132240719,132240801⟩,
⟨64,353458856,353459072⟩]
theorem checked35761 : checkPrefixCuts (2^48) 4691197953 10 Manual.Count131072.C035761.packed 64 cuts35761 = true := by
 decide +kernel
def pointBounds35761 : List (Nat × Nat × Nat) := [(4691247104,107455147796423,107455532447740)]
theorem point_links_checked35761 : (cuts35761.take 1).map (fun c => (4691197953-1+2*2^10*c.k,107455015555704+c.lower,107455400206939+c.upper)) = pointBounds35761 := by
 decide +kernel
def cuts35762 : List PrefixCut := [⟨32,177235702,177235812⟩,
⟨64,356148874,356149096⟩]
theorem checked35762 : checkPrefixCuts (2^48) 4691329025 10 Manual.Count131072.C035762.packed 64 cuts35762 = true := by
 decide +kernel
def pointBounds35762 : List (Nat × Nat × Nat) := [(4691394560,107455546250262,107455930901823)]
theorem point_links_checked35762 : (cuts35762.take 1).map (fun c => (4691329025-1+2*2^10*c.k,107455369014560+c.lower,107455753666011+c.upper)) = pointBounds35762 := by
 decide +kernel
def cuts35763 : List PrefixCut := [⟨40,220668120,220668259⟩,
⟨64,352479170,352479389⟩]
theorem checked35763 : checkPrefixCuts (2^48) 4691460097 10 Manual.Count131072.C035763.packed 64 cuts35763 = true := by
 decide +kernel
def pointBounds35763 : List (Nat × Nat × Nat) := [(4691542016,107455945831554,107456330483366)]
theorem point_links_checked35763 : (cuts35763.take 1).map (fun c => (4691460097-1+2*2^10*c.k,107455725163434+c.lower,107456109815107+c.upper)) = pointBounds35763 := by
 decide +kernel
def cuts35764 : List PrefixCut := [⟨48,265477791,265477959⟩,
⟨64,353429212,353429433⟩]
theorem checked35764 : checkPrefixCuts (2^48) 4691591169 10 Manual.Count131072.C035764.packed 64 cuts35764 = true := by
 decide +kernel
def pointBounds35764 : List (Nat × Nat × Nat) := [(4691689472,107456343120395,107456727772455)]
theorem point_links_checked35764 : (cuts35764.take 1).map (fun c => (4691591169-1+2*2^10*c.k,107456077642604+c.lower,107456462294496+c.upper)) = pointBounds35764 := by
 decide +kernel
def cuts35765 : List PrefixCut := [⟨56,313224536,313224734⟩,
⟨64,357678880,357679104⟩]
theorem checked35765 : checkPrefixCuts (2^48) 4691722241 10 Manual.Count131072.C035765.packed 64 cuts35765 = true := by
 decide +kernel
def pointBounds35765 : List (Nat × Nat × Nat) := [(4691836928,107456744296352,107457128948663)]
theorem point_links_checked35765 : (cuts35765.take 1).map (fun c => (4691722241-1+2*2^10*c.k,107456431071816+c.lower,107456815723929+c.upper)) = pointBounds35765 := by
 decide +kernel
def cuts35766 : List PrefixCut := [⟨64,355089246,355089464⟩]
theorem checked35766 : checkPrefixCuts (2^48) 4691853313 10 Manual.Count131072.C035766.packed 64 cuts35766 = true := by
 decide +kernel
def pointBounds35766 : List (Nat × Nat × Nat) := [(4691984384,107457143839942,107457528492497)]
theorem point_links_checked35766 : (cuts35766.take 1).map (fun c => (4691853313-1+2*2^10*c.k,107456788750696+c.lower,107457173403033+c.upper)) = pointBounds35766 := by
 decide +kernel
def cuts35767 : List PrefixCut := [⟨64,349680231,349680446⟩]
theorem checked35767 : checkPrefixCuts (2^48) 4691984385 10 Manual.Count131072.C035767.packed 64 cuts35767 = true := by
 decide +kernel
def cuts35768 : List PrefixCut := [⟨8,43551873,43551900⟩,
⟨64,353449733,353449954⟩]
theorem checked35768 : checkPrefixCuts (2^48) 4692115457 10 Manual.Count131072.C035768.packed 64 cuts35768 = true := by
 decide +kernel
def pointBounds35768 : List (Nat × Nat × Nat) := [(4692131840,107457537072046,107457921724843)]
theorem point_links_checked35768 : (cuts35768.take 1).map (fun c => (4692115457-1+2*2^10*c.k,107457493520173+c.lower,107457878172943+c.upper)) = pointBounds35768 := by
 decide +kernel
def cuts35769 : List PrefixCut := [⟨16,90340462,90340513⟩,
⟨64,353979762,353979978⟩]
theorem checked35769 : checkPrefixCuts (2^48) 4692246529 10 Manual.Count131072.C035769.packed 64 cuts35769 = true := by
 decide +kernel
def pointBounds35769 : List (Nat × Nat × Nat) := [(4692279296,107457937310368,107458321963410)]
theorem point_links_checked35769 : (cuts35769.take 1).map (fun c => (4692246529-1+2*2^10*c.k,107457846969906+c.lower,107458231622897+c.upper)) = pointBounds35769 := by
 decide +kernel
def cuts35770 : List PrefixCut := [⟨24,132267457,132267541⟩,
⟨64,356909063,356909279⟩]
theorem checked35770 : checkPrefixCuts (2^48) 4692377601 10 Manual.Count131072.C035770.packed 64 cuts35770 = true := by
 decide +kernel
def pointBounds35770 : List (Nat × Nat × Nat) := [(4692426752,107458333217125,107458717870416)]
theorem point_links_checked35770 : (cuts35770.take 1).map (fun c => (4692377601-1+2*2^10*c.k,107458200949668+c.lower,107458585602875+c.upper)) = pointBounds35770 := by
 decide +kernel
def cuts35771 : List PrefixCut := [⟨32,175631579,175631689⟩,
⟨64,352400397,352400616⟩]
theorem checked35771 : checkPrefixCuts (2^48) 4692508673 10 Manual.Count131072.C035771.packed 64 cuts35771 = true := by
 decide +kernel
def pointBounds35771 : List (Nat × Nat × Nat) := [(4692574208,107458733490310,107459118143843)]
theorem point_links_checked35771 : (cuts35771.take 1).map (fun c => (4692508673-1+2*2^10*c.k,107458557858731+c.lower,107458942512154+c.upper)) = pointBounds35771 := by
 decide +kernel
def cuts35772 : List PrefixCut := [⟨40,221932242,221932375⟩,
⟨64,351670806,351671019⟩]
theorem checked35772 : checkPrefixCuts (2^48) 4692639745 10 Manual.Count131072.C035772.packed 64 cuts35772 = true := by
 decide +kernel
def pointBounds35772 : List (Nat × Nat × Nat) := [(4692721664,107459132191370,107459516845145)]
theorem point_links_checked35772 : (cuts35772.take 1).map (fun c => (4692639745-1+2*2^10*c.k,107458910259128+c.lower,107459294912770+c.upper)) = pointBounds35772 := by
 decide +kernel
def cuts35773 : List PrefixCut := [⟨48,262232136,262232301⟩,
⟨64,350581299,350581521⟩]
theorem checked35773 : checkPrefixCuts (2^48) 4692770817 10 Manual.Count131072.C035773.packed 64 cuts35773 = true := by
 decide +kernel
def pointBounds35773 : List (Nat × Nat × Nat) := [(4692869120,107459524162070,107459908816090)]
theorem point_links_checked35773 : (cuts35773.take 1).map (fun c => (4692770817-1+2*2^10*c.k,107459261929934+c.lower,107459646583789+c.upper)) = pointBounds35773 := by
 decide +kernel
def cuts35774 : List PrefixCut := [⟨56,307987660,307987846⟩,
⟨64,351771079,351771292⟩]
theorem checked35774 : checkPrefixCuts (2^48) 4692901889 10 Manual.Count131072.C035774.packed 64 cuts35774 = true := by
 decide +kernel
def pointBounds35774 : List (Nat × Nat × Nat) := [(4693016576,107459920498893,107460305153156)]
theorem point_links_checked35774 : (cuts35774.take 1).map (fun c => (4692901889-1+2*2^10*c.k,107459612511233+c.lower,107459997165310+c.upper)) = pointBounds35774 := by
 decide +kernel
def cuts35775 : List PrefixCut := [⟨64,349182265,349182483⟩]
theorem checked35775 : checkPrefixCuts (2^48) 4693032961 10 Manual.Count131072.C035775.packed 64 cuts35775 = true := by
 decide +kernel
def pointBounds35775 : List (Nat × Nat × Nat) := [(4693164032,107460313464577,107460698119085)]
theorem point_links_checked35775 : (cuts35775.take 1).map (fun c => (4693032961-1+2*2^10*c.k,107459964282312+c.lower,107460348936602+c.upper)) = pointBounds35775 := by
 decide +kernel
def cuts35776 : List PrefixCut := [⟨64,349292479,349292698⟩]
theorem checked35776 : checkPrefixCuts (2^48) 4693164033 10 Manual.Count131072.C035776.packed 64 cuts35776 = true := by
 decide +kernel
def cuts35777 : List PrefixCut := [⟨8,44020715,44020744⟩,
⟨64,351801566,351801790⟩]
theorem checked35777 : checkPrefixCuts (2^48) 4693295105 10 Manual.Count131072.C035777.packed 64 cuts35777 = true := by
 decide +kernel
def pointBounds35777 : List (Nat × Nat × Nat) := [(4693311488,107460706777771,107461091432527)]
theorem point_links_checked35777 : (cuts35777.take 1).map (fun c => (4693295105-1+2*2^10*c.k,107460662757056+c.lower,107461047411783+c.upper)) = pointBounds35777 := by
 decide +kernel
def cuts35778 : List PrefixCut := [⟨16,88518595,88518651⟩,
⟨64,351371983,351372200⟩]
theorem checked35778 : checkPrefixCuts (2^48) 4693426177 10 Manual.Count131072.C035778.packed 64 cuts35778 = true := by
 decide +kernel
def pointBounds35778 : List (Nat × Nat × Nat) := [(4693458944,107461103077217,107461487732224)]
theorem point_links_checked35778 : (cuts35778.take 1).map (fun c => (4693426177-1+2*2^10*c.k,107461014558622+c.lower,107461399213573+c.upper)) = pointBounds35778 := by
 decide +kernel
def cuts35779 : List PrefixCut := [⟨24,133133774,133133859⟩,
⟨64,351961842,351962064⟩]
theorem checked35779 : checkPrefixCuts (2^48) 4693557249 10 Manual.Count131072.C035779.packed 64 cuts35779 = true := by
 decide +kernel
def pointBounds35779 : List (Nat × Nat × Nat) := [(4693606400,107461499064379,107461883719632)]
theorem point_links_checked35779 : (cuts35779.take 1).map (fun c => (4693557249-1+2*2^10*c.k,107461365930605+c.lower,107461750585773+c.upper)) = pointBounds35779 := by
 decide +kernel
def cuts35780 : List PrefixCut := [⟨32,175887289,175887397⟩,
⟨64,349253476,349253694⟩]
theorem checked35780 : checkPrefixCuts (2^48) 4693688321 10 Manual.Count131072.C035780.packed 64 cuts35780 = true := by
 decide +kernel
def pointBounds35780 : List (Nat × Nat × Nat) := [(4693753856,107461893779736,107462278435234)]
theorem point_links_checked35780 : (cuts35780.take 1).map (fun c => (4693688321-1+2*2^10*c.k,107461717892447+c.lower,107462102547837+c.upper)) = pointBounds35780 := by
 decide +kernel
def cuts35781 : List PrefixCut := [⟨40,215699903,215700039⟩,
⟨64,350203134,350203354⟩]
theorem checked35781 : checkPrefixCuts (2^48) 4693819393 10 Manual.Count131072.C035781.packed 64 cuts35781 = true := by
 decide +kernel
def pointBounds35781 : List (Nat × Nat × Nat) := [(4693901312,107462282845826,107462667501570)]
theorem point_links_checked35781 : (cuts35781.take 1).map (fun c => (4693819393-1+2*2^10*c.k,107462067145923+c.lower,107462451801531+c.upper)) = pointBounds35781 := by
 decide +kernel
def cuts35782 : List PrefixCut := [⟨48,266903460,266903620⟩,
⟨64,357149269,357149486⟩]
theorem checked35782 : checkPrefixCuts (2^48) 4693950465 10 Manual.Count131072.C035782.packed 64 cuts35782 = true := by
 decide +kernel
def pointBounds35782 : List (Nat × Nat × Nat) := [(4694048768,107462684252517,107463068908505)]
theorem point_links_checked35782 : (cuts35782.take 1).map (fun c => (4693950465-1+2*2^10*c.k,107462417349057+c.lower,107462802004885+c.upper)) = pointBounds35782 := by
 decide +kernel
def cuts35783 : List PrefixCut := [⟨56,305211905,305212095⟩,
⟨64,348144850,348145068⟩]
theorem checked35783 : checkPrefixCuts (2^48) 4694081537 10 Manual.Count131072.C035783.packed 64 cuts35783 = true := by
 decide +kernel
def pointBounds35783 : List (Nat × Nat × Nat) := [(4694196224,107463079710231,107463464366466)]
theorem point_links_checked35783 : (cuts35783.take 1).map (fun c => (4694081537-1+2*2^10*c.k,107462774498326+c.lower,107463159154371+c.upper)) = pointBounds35783 := by
 decide +kernel
def cuts35784 : List PrefixCut := [⟨64,354970719,354970941⟩]
theorem checked35784 : checkPrefixCuts (2^48) 4694212609 10 Manual.Count131072.C035784.packed 64 cuts35784 = true := by
 decide +kernel
def pointBounds35784 : List (Nat × Nat × Nat) := [(4694343680,107463477613895,107463862270380)]
theorem point_links_checked35784 : (cuts35784.take 1).map (fun c => (4694212609-1+2*2^10*c.k,107463122643176+c.lower,107463507299439+c.upper)) = pointBounds35784 := by
 decide +kernel
def cuts35785 : List PrefixCut := [⟨64,357419172,357419394⟩]
theorem checked35785 : checkPrefixCuts (2^48) 4694343681 10 Manual.Count131072.C035785.packed 64 cuts35785 = true := by
 decide +kernel
def cuts35786 : List PrefixCut := [⟨8,43829777,43829806⟩,
⟨64,352072909,352073134⟩]
theorem checked35786 : checkPrefixCuts (2^48) 4694474753 10 Manual.Count131072.C035786.packed 64 cuts35786 = true := by
 decide +kernel
def pointBounds35786 : List (Nat × Nat × Nat) := [(4694491136,107463878862844,107464263519580)]
theorem point_links_checked35786 : (cuts35786.take 1).map (fun c => (4694474753-1+2*2^10*c.k,107463835033067+c.lower,107464219689774+c.upper)) = pointBounds35786 := by
 decide +kernel
def cuts35787 : List PrefixCut := [⟨16,91194415,91194470⟩,
⟨64,355120922,355121144⟩]
theorem checked35787 : checkPrefixCuts (2^48) 4694605825 10 Manual.Count131072.C035787.packed 64 cuts35787 = true := by
 decide +kernel
def pointBounds35787 : List (Nat × Nat × Nat) := [(4694638592,107464278300391,107464662957378)]
theorem point_links_checked35787 : (cuts35787.take 1).map (fun c => (4694605825-1+2*2^10*c.k,107464187105976+c.lower,107464571762908+c.upper)) = pointBounds35787 := by
 decide +kernel
def cuts35788 : List PrefixCut := [⟨24,134419339,134419422⟩,
⟨64,359667505,359667725⟩]
theorem checked35788 : checkPrefixCuts (2^48) 4694736897 10 Manual.Count131072.C035788.packed 64 cuts35788 = true := by
 decide +kernel
def pointBounds35788 : List (Nat × Nat × Nat) := [(4694786048,107464676646237,107465061303474)]
theorem point_links_checked35788 : (cuts35788.take 1).map (fun c => (4694736897-1+2*2^10*c.k,107464542226898+c.lower,107464926884052+c.upper)) = pointBounds35788 := by
 decide +kernel
def cuts35789 : List PrefixCut := [⟨32,175723188,175723295⟩,
⟨64,354501503,354501721⟩]
theorem checked35789 : checkPrefixCuts (2^48) 4694867969 10 Manual.Count131072.C035789.packed 64 cuts35789 = true := by
 decide +kernel
def pointBounds35789 : List (Nat × Nat × Nat) := [(4694933504,107465077617591,107465462275072)]
theorem point_links_checked35789 : (cuts35789.take 1).map (fun c => (4694867969-1+2*2^10*c.k,107464901894403+c.lower,107465286551777+c.upper)) = pointBounds35789 := by
 decide +kernel
def cuts35790 : List PrefixCut := [⟨40,219962216,219962350⟩,
⟨64,352633134,352633350⟩]
theorem checked35790 : checkPrefixCuts (2^48) 4694999041 10 Manual.Count131072.C035790.packed 64 cuts35790 = true := by
 decide +kernel
def pointBounds35790 : List (Nat × Nat × Nat) := [(4695080960,107465476358122,107465861015848)]
theorem point_links_checked35790 : (cuts35790.take 1).map (fun c => (4694999041-1+2*2^10*c.k,107465256395906+c.lower,107465641053498+c.upper)) = pointBounds35790 := by
 decide +kernel
def cuts35791 : List PrefixCut := [⟨48,264198617,264198780⟩,
⟨64,352203647,352203863⟩]
theorem checked35791 : checkPrefixCuts (2^48) 4695130113 10 Manual.Count131072.C035791.packed 64 cuts35791 = true := by
 decide +kernel
def pointBounds35791 : List (Nat × Nat × Nat) := [(4695228416,107465873227657,107466257885628)]
theorem point_links_checked35791 : (cuts35791.take 1).map (fun c => (4695130113-1+2*2^10*c.k,107465609029040+c.lower,107465993686848+c.upper)) = pointBounds35791 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000180
