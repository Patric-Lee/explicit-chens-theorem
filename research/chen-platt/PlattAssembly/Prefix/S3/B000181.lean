import PlattAssemblyKernel
import PlattCertificates.Count131072.C025792
import PlattCertificates.Count131072.C025793
import PlattCertificates.Count131072.C025794
import PlattCertificates.Count131072.C025795
import PlattCertificates.Count131072.C025796
import PlattCertificates.Count131072.C025797
import PlattCertificates.Count131072.C025798
import PlattCertificates.Count131072.C025799
import PlattCertificates.Count131072.C025800
import PlattCertificates.Count131072.C025801
import PlattCertificates.Count131072.C025802
import PlattCertificates.Count131072.C025803
import PlattCertificates.Count131072.C025804
import PlattCertificates.Count131072.C025805
import PlattCertificates.Count131072.C025806
import PlattCertificates.Count131072.C025807
import PlattCertificates.Count131072.C025808
import PlattCertificates.Count131072.C025809
import PlattCertificates.Count131072.C025810
import PlattCertificates.Count131072.C025811
import PlattCertificates.Count131072.C025812
import PlattCertificates.Count131072.C025813
import PlattCertificates.Count131072.C025814
import PlattCertificates.Count131072.C025815
import PlattCertificates.Count131072.C025816
import PlattCertificates.Count131072.C025817
import PlattCertificates.Count131072.C025818
import PlattCertificates.Count131072.C025819
import PlattCertificates.Count131072.C025820
import PlattCertificates.Count131072.C025821
import PlattCertificates.Count131072.C025822
import PlattCertificates.Count131072.C025823
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000181
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts25792 : List PrefixCut := [⟨78,306791582,306791751⟩,
⟨128,499561733,499562013⟩]
theorem checked25792 : checkPrefixCuts (2^48) 3384541185 9 Manual.Count131072.C025792.packed 128 cuts25792 = true := by
 decide +kernel
def pointBounds25792 : List (Nat × Nat × Nat) := [(3384621056,103298163239181,103298545479869)]
theorem point_links_checked25792 : (cuts25792.take 1).map (fun c => (3384541185-1+2*2^9*c.k,103297856447599+c.lower,103298238688118+c.upper)) = pointBounds25792 := by
 decide +kernel
def cuts25793 : List PrefixCut := [⟨54,206322347,206322461⟩,
⟨128,490976829,490977102⟩]
theorem checked25793 : checkPrefixCuts (2^48) 3384672257 9 Manual.Count131072.C025793.packed 128 cuts25793 = true := by
 decide +kernel
def pointBounds25793 : List (Nat × Nat × Nat) := [(3384727552,103298562331679,103298944572592)]
theorem point_links_checked25793 : (cuts25793.take 1).map (fun c => (3384672257-1+2*2^9*c.k,103298356009332+c.lower,103298738250131+c.upper)) = pointBounds25793 := by
 decide +kernel
def cuts25794 : List PrefixCut := [⟨30,115672835,115672900⟩,
⟨128,494200868,494201151⟩]
theorem checked25794 : checkPrefixCuts (2^48) 3384803329 9 Manual.Count131072.C025794.packed 128 cuts25794 = true := by
 decide +kernel
def pointBounds25794 : List (Nat × Nat × Nat) := [(3384834048,103298962658996,103299344900133)]
theorem point_links_checked25794 : (cuts25794.take 1).map (fun c => (3384803329-1+2*2^9*c.k,103298846986161+c.lower,103299229227233+c.upper)) = pointBounds25794 := by
 decide +kernel
def cuts25795 : List PrefixCut := [⟨6,22701348,22701361⟩,
⟨110,427660062,427660309⟩,
⟨128,498921496,498921784⟩]
theorem checked25795 : checkPrefixCuts (2^48) 3384934401 9 Manual.Count131072.C025795.packed 128 cuts25795 = true := by
 decide +kernel
def pointBounds25795 : List (Nat × Nat × Nat) := [(3384940544,103299363888377,103299746129745),(3385047040,103299768847091,103300151088693)]
theorem point_links_checked25795 : (cuts25795.take 2).map (fun c => (3384934401-1+2*2^9*c.k,103299341187029+c.lower,103299723428384+c.upper)) = pointBounds25795 := by
 decide +kernel
def cuts25796 : List PrefixCut := [⟨86,330441670,330441862⟩,
⟨128,493746884,493747165⟩]
theorem checked25796 : checkPrefixCuts (2^48) 3385065473 9 Manual.Count131072.C025796.packed 128 cuts25796 = true := by
 decide +kernel
def pointBounds25796 : List (Nat × Nat × Nat) := [(3385153536,103300170550195,103300552792030)]
theorem point_links_checked25796 : (cuts25796.take 1).map (fun c => (3385065473-1+2*2^9*c.k,103299840108525+c.lower,103300222350168+c.upper)) = pointBounds25796 := by
 decide +kernel
def cuts25797 : List PrefixCut := [⟨62,241877461,241877596⟩,
⟨128,499298600,499298880⟩]
theorem checked25797 : checkPrefixCuts (2^48) 3385196545 9 Manual.Count131072.C025797.packed 128 cuts25797 = true := by
 decide +kernel
def pointBounds25797 : List (Nat × Nat × Nat) := [(3385260032,103300575732870,103300957974929)]
theorem point_links_checked25797 : (cuts25797.take 1).map (fun c => (3385196545-1+2*2^9*c.k,103300333855409+c.lower,103300716097333+c.upper)) = pointBounds25797 := by
 decide +kernel
def cuts25798 : List PrefixCut := [⟨38,148330786,148330870⟩,
⟨128,503020762,503021044⟩]
theorem checked25798 : checkPrefixCuts (2^48) 3385327617 9 Manual.Count131072.C025798.packed 128 cuts25798 = true := by
 decide +kernel
def pointBounds25798 : List (Nat × Nat × Nat) := [(3385366528,103300981484795,103301363727083)]
theorem point_links_checked25798 : (cuts25798.take 1).map (fun c => (3385327617-1+2*2^9*c.k,103300833154009+c.lower,103301215396213+c.upper)) = pointBounds25798 := by
 decide +kernel
def cuts25799 : List PrefixCut := [⟨14,52712121,52712151⟩,
⟨118,452286163,452286418⟩,
⟨128,490447069,490447346⟩]
theorem checked25799 : checkPrefixCuts (2^48) 3385458689 9 Manual.Count131072.C025799.packed 128 cuts25799 = true := by
 decide +kernel
def pointBounds25799 : List (Nat × Nat × Nat) := [(3385473024,103301388886892,103301771129408),(3385579520,103301788460934,103302170703675)]
theorem point_links_checked25799 : (cuts25799.take 2).map (fun c => (3385458689-1+2*2^9*c.k,103301336174771+c.lower,103301718417257+c.upper)) = pointBounds25799 := by
 decide +kernel
def cuts25800 : List PrefixCut := [⟨94,365058658,365058867⟩,
⟨128,496330899,496331177⟩]
theorem checked25800 : checkPrefixCuts (2^48) 3385589761 9 Manual.Count131072.C025800.packed 128 cuts25800 = true := by
 decide +kernel
def pointBounds25800 : List (Nat × Nat × Nat) := [(3385686016,103302191680498,103302573923470)]
theorem point_links_checked25800 : (cuts25800.take 1).map (fun c => (3385589761-1+2*2^9*c.k,103301826621840+c.lower,103302208864603+c.upper)) = pointBounds25800 := by
 decide +kernel
def cuts25801 : List PrefixCut := [⟨70,274012982,274013130⟩,
⟨128,502047882,502048157⟩]
theorem checked25801 : checkPrefixCuts (2^48) 3385720833 9 Manual.Count131072.C025801.packed 128 cuts25801 = true := by
 decide +kernel
def pointBounds25801 : List (Nat × Nat × Nat) := [(3385792512,103302596965721,103302979208910)]
theorem point_links_checked25801 : (cuts25801.take 1).map (fun c => (3385720833-1+2*2^9*c.k,103302322952739+c.lower,103302705195780+c.upper)) = pointBounds25801 := by
 decide +kernel
def cuts25802 : List PrefixCut := [⟨46,177653259,177653362⟩,
⟨128,492218961,492219240⟩]
theorem checked25802 : checkPrefixCuts (2^48) 3385851905 9 Manual.Count131072.C025802.packed 128 cuts25802 = true := by
 decide +kernel
def pointBounds25802 : List (Nat × Nat × Nat) := [(3385899008,103303002653880,103303384897299)]
theorem point_links_checked25802 : (cuts25802.take 1).map (fun c => (3385851905-1+2*2^9*c.k,103302825000621+c.lower,103303207243937+c.upper)) = pointBounds25802 := by
 decide +kernel
def cuts25803 : List PrefixCut := [⟨22,88283183,88283231⟩,
⟨126,492283257,492283528⟩,
⟨128,500180251,500180527⟩]
theorem checked25803 : checkPrefixCuts (2^48) 3385982977 9 Manual.Count131072.C025803.packed 128 cuts25803 = true := by
 decide +kernel
def pointBounds25803 : List (Nat × Nat × Nat) := [(3386005504,103303405502765,103303787746408),(3386112000,103303809502839,103304191746705)]
theorem point_links_checked25803 : (cuts25803.take 2).map (fun c => (3385982977-1+2*2^9*c.k,103303317219582+c.lower,103303699463177+c.upper)) = pointBounds25803 := by
 decide +kernel
def cuts25804 : List PrefixCut := [⟨102,393264116,393264331⟩,
⟨128,495755200,495755471⟩]
theorem checked25804 : checkPrefixCuts (2^48) 3386114049 9 Manual.Count131072.C025804.packed 128 cuts25804 = true := by
 decide +kernel
def pointBounds25804 : List (Nat × Nat × Nat) := [(3386218496,103304210663949,103304592908035)]
theorem point_links_checked25804 : (cuts25804.take 1).map (fun c => (3386114049-1+2*2^9*c.k,103303817399833+c.lower,103304199643704+c.upper)) = pointBounds25804 := by
 decide +kernel
def cuts25805 : List PrefixCut := [⟨78,301068037,301068208⟩,
⟨128,499144011,499144292⟩]
theorem checked25805 : checkPrefixCuts (2^48) 3386245121 9 Manual.Count131072.C025805.packed 128 cuts25805 = true := by
 decide +kernel
def pointBounds25805 : List (Nat × Nat × Nat) := [(3386324992,103304614223070,103304996467383)]
theorem point_links_checked25805 : (cuts25805.take 1).map (fun c => (3386245121-1+2*2^9*c.k,103304313155033+c.lower,103304695399175+c.upper)) = pointBounds25805 := by
 decide +kernel
def cuts25806 : List PrefixCut := [⟨54,215029160,215029279⟩,
⟨128,499623506,499623783⟩]
theorem checked25806 : checkPrefixCuts (2^48) 3386376193 9 Manual.Count131072.C025806.packed 128 cuts25806 = true := by
 decide +kernel
def pointBounds25806 : List (Nat × Nat × Nat) := [(3386431488,103305027328204,103305409572746)]
theorem point_links_checked25806 : (cuts25806.take 1).map (fun c => (3386376193-1+2*2^9*c.k,103304812299044+c.lower,103305194543467+c.upper)) = pointBounds25806 := by
 decide +kernel
def cuts25807 : List PrefixCut := [⟨30,117941889,117941956⟩,
⟨128,493786086,493786364⟩]
theorem checked25807 : checkPrefixCuts (2^48) 3386507265 9 Manual.Count131072.C025807.packed 128 cuts25807 = true := by
 decide +kernel
def pointBounds25807 : List (Nat × Nat × Nat) := [(3386537984,103305429864439,103305812109206)]
theorem point_links_checked25807 : (cuts25807.take 1).map (fun c => (3386507265-1+2*2^9*c.k,103305311922550+c.lower,103305694167250+c.upper)) = pointBounds25807 := by
 decide +kernel
def cuts25808 : List PrefixCut := [⟨6,24352192,24352205⟩,
⟨110,424868496,424868736⟩,
⟨128,497506953,497507232⟩]
theorem checked25808 : checkPrefixCuts (2^48) 3386638337 9 Manual.Count131072.C025808.packed 128 cuts25808 = true := by
 decide +kernel
def pointBounds25808 : List (Nat × Nat × Nat) := [(3386644480,103305830060828,103306212305819),(3386750976,103306230577132,103306612822350)]
theorem point_links_checked25808 : (cuts25808.take 2).map (fun c => (3386638337-1+2*2^9*c.k,103305805708636+c.lower,103306187953614+c.upper)) = pointBounds25808 := by
 decide +kernel
def cuts25809 : List PrefixCut := [⟨86,337173470,337173659⟩,
⟨128,497321539,497321817⟩]
theorem checked25809 : checkPrefixCuts (2^48) 3386769409 9 Manual.Count131072.C025809.packed 128 cuts25809 = true := by
 decide +kernel
def pointBounds25809 : List (Nat × Nat × Nat) := [(3386857472,103306640389059,103307022634505)]
theorem point_links_checked25809 : (cuts25809.take 1).map (fun c => (3386769409-1+2*2^9*c.k,103306303215589+c.lower,103306685460846+c.upper)) = pointBounds25809 := by
 decide +kernel
def cuts25810 : List PrefixCut := [⟨62,237849802,237849938⟩,
⟨128,497717715,497717996⟩]
theorem checked25810 : checkPrefixCuts (2^48) 3386900481 9 Manual.Count131072.C025810.packed 128 cuts25810 = true := by
 decide +kernel
def pointBounds25810 : List (Nat × Nat × Nat) := [(3386963968,103307038386930,103307420632601)]
theorem point_links_checked25810 : (cuts25810.take 1).map (fun c => (3386900481-1+2*2^9*c.k,103306800537128+c.lower,103307182782663+c.upper)) = pointBounds25810 := by
 decide +kernel
def cuts25811 : List PrefixCut := [⟨38,149918250,149918331⟩,
⟨128,502435359,502435642⟩]
theorem checked25811 : checkPrefixCuts (2^48) 3387031553 9 Manual.Count131072.C025811.packed 128 cuts25811 = true := by
 decide +kernel
def pointBounds25811 : List (Nat × Nat × Nat) := [(3387070464,103307448173093,103307830418990)]
theorem point_links_checked25811 : (cuts25811.take 1).map (fun c => (3387031553-1+2*2^9*c.k,103307298254843+c.lower,103307680500659+c.upper)) = pointBounds25811 := by
 decide +kernel
def cuts25812 : List PrefixCut := [⟨14,53350408,53350437⟩,
⟨118,454717790,454718044⟩,
⟨128,492610208,492610484⟩]
theorem checked25812 : checkPrefixCuts (2^48) 3387162625 9 Manual.Count131072.C025812.packed 128 cuts25812 = true := by
 decide +kernel
def pointBounds25812 : List (Nat × Nat × Nat) := [(3387176960,103307854040610,103308236286738),(3387283456,103308255407992,103308637654345)]
theorem point_links_checked25812 : (cuts25812.take 2).map (fun c => (3387162625-1+2*2^9*c.k,103307800690202+c.lower,103308182936301+c.upper)) = pointBounds25812 := by
 decide +kernel
def cuts25813 : List PrefixCut := [⟨94,366703075,366703285⟩,
⟨128,496081199,496081482⟩]
theorem checked25813 : checkPrefixCuts (2^48) 3387293697 9 Manual.Count131072.C025813.packed 128 cuts25813 = true := by
 decide +kernel
def pointBounds25813 : List (Nat × Nat × Nat) := [(3387389952,103308660003485,103309042250070)]
theorem point_links_checked25813 : (cuts25813.take 1).map (fun c => (3387293697-1+2*2^9*c.k,103308293300410+c.lower,103308675546785+c.upper)) = pointBounds25813 := by
 decide +kernel
def cuts25814 : List PrefixCut := [⟨70,272213236,272213389⟩,
⟨128,495729561,495729841⟩]
theorem checked25814 : checkPrefixCuts (2^48) 3387424769 9 Manual.Count131072.C025814.packed 128 cuts25814 = true := by
 decide +kernel
def pointBounds25814 : List (Nat × Nat × Nat) := [(3387496448,103309061594845,103309443841656)]
theorem point_links_checked25814 : (cuts25814.take 1).map (fun c => (3387424769-1+2*2^9*c.k,103308789381609+c.lower,103309171628267+c.upper)) = pointBounds25814 := by
 decide +kernel
def cuts25815 : List PrefixCut := [⟨46,177730106,177730207⟩,
⟨128,496458270,496458550⟩]
theorem checked25815 : checkPrefixCuts (2^48) 3387555841 9 Manual.Count131072.C025815.packed 128 cuts25815 = true := by
 decide +kernel
def pointBounds25815 : List (Nat × Nat × Nat) := [(3387602944,103309462841276,103309845088315)]
theorem point_links_checked25815 : (cuts25815.take 1).map (fun c => (3387555841-1+2*2^9*c.k,103309285111170+c.lower,103309667358108+c.upper)) = pointBounds25815 := by
 decide +kernel
def cuts25816 : List PrefixCut := [⟨22,83087354,83087402⟩,
⟨126,486136467,486136747⟩,
⟨128,494029490,494029774⟩]
theorem checked25816 : checkPrefixCuts (2^48) 3387686913 9 Manual.Count131072.C025816.packed 128 cuts25816 = true := by
 decide +kernel
def pointBounds25816 : List (Nat × Nat × Nat) := [(3387709440,103309864656794,103310246904060),(3387815936,103310267705907,103310649953405)]
theorem point_links_checked25816 : (cuts25816.take 2).map (fun c => (3387686913-1+2*2^9*c.k,103309781569440+c.lower,103310163816658+c.upper)) = pointBounds25816 := by
 decide +kernel
def cuts25817 : List PrefixCut := [⟨102,398549820,398550044⟩,
⟨128,496336783,496337063⟩]
theorem checked25817 : checkPrefixCuts (2^48) 3387817985 9 Manual.Count131072.C025817.packed 128 cuts25817 = true := by
 decide +kernel
def pointBounds25817 : List (Nat × Nat × Nat) := [(3387922432,103310674148750,103311056396476)]
theorem point_links_checked25817 : (cuts25817.take 1).map (fun c => (3387817985-1+2*2^9*c.k,103310275598930+c.lower,103310657846432+c.upper)) = pointBounds25817 := by
 decide +kernel
def cuts25818 : List PrefixCut := [⟨78,301996619,301996793⟩,
⟨128,499806808,499807093⟩]
theorem checked25818 : checkPrefixCuts (2^48) 3387949057 9 Manual.Count131072.C025818.packed 128 cuts25818 = true := by
 decide +kernel
def pointBounds25818 : List (Nat × Nat × Nat) := [(3388028928,103311073932332,103311456180288)]
theorem point_links_checked25818 : (cuts25818.take 1).map (fun c => (3387949057-1+2*2^9*c.k,103310771935713+c.lower,103311154183495+c.upper)) = pointBounds25818 := by
 decide +kernel
def cuts25819 : List PrefixCut := [⟨54,209520975,209521097⟩,
⟨128,498707532,498707819⟩]
theorem checked25819 : checkPrefixCuts (2^48) 3388080129 9 Manual.Count131072.C025819.packed 128 cuts25819 = true := by
 decide +kernel
def pointBounds25819 : List (Nat × Nat × Nat) := [(3388135424,103311481263496,103311863511685)]
theorem point_links_checked25819 : (cuts25819.take 1).map (fun c => (3388080129-1+2*2^9*c.k,103311271742521+c.lower,103311653990588+c.upper)) = pointBounds25819 := by
 decide +kernel
def cuts25820 : List PrefixCut := [⟨30,116304165,116304234⟩,
⟨128,502177314,502177600⟩]
theorem checked25820 : checkPrefixCuts (2^48) 3388211201 9 Manual.Count131072.C025820.packed 128 cuts25820 = true := by
 decide +kernel
def pointBounds25820 : List (Nat × Nat × Nat) := [(3388241920,103311886754218,103312269002641)]
theorem point_links_checked25820 : (cuts25820.take 1).map (fun c => (3388211201-1+2*2^9*c.k,103311770450053+c.lower,103312152698407+c.upper)) = pointBounds25820 := by
 decide +kernel
def cuts25821 : List PrefixCut := [⟨6,23343087,23343099⟩,
⟨110,422245770,422246004⟩,
⟨128,493020196,493020469⟩]
theorem checked25821 : checkPrefixCuts (2^48) 3388342273 9 Manual.Count131072.C025821.packed 128 cuts25821 = true := by
 decide +kernel
def pointBounds25821 : List (Nat × Nat × Nat) := [(3388348416,103312295970454,103312678219106),(3388454912,103312694873137,103313077122011)]
theorem point_links_checked25821 : (cuts25821.take 2).map (fun c => (3388342273-1+2*2^9*c.k,103312272627367+c.lower,103312654876007+c.upper)) = pointBounds25821 := by
 decide +kernel
def cuts25822 : List PrefixCut := [⟨86,326122179,326122363⟩,
⟨128,489761528,489761808⟩]
theorem checked25822 : checkPrefixCuts (2^48) 3388473345 9 Manual.Count131072.C025822.packed 128 cuts25822 = true := by
 decide +kernel
def pointBounds25822 : List (Nat × Nat × Nat) := [(3388561408,103313091769742,103313474018839)]
theorem point_links_checked25822 : (cuts25822.take 1).map (fun c => (3388473345-1+2*2^9*c.k,103312765647563+c.lower,103313147896476+c.upper)) = pointBounds25822 := by
 decide +kernel
def cuts25823 : List PrefixCut := [⟨62,241301959,241302091⟩,
⟨128,494726418,494726697⟩]
theorem checked25823 : checkPrefixCuts (2^48) 3388604417 9 Manual.Count131072.C025823.packed 128 cuts25823 = true := by
 decide +kernel
def pointBounds25823 : List (Nat × Nat × Nat) := [(3388667904,103313496711050,103313878960375)]
theorem point_links_checked25823 : (cuts25823.take 1).map (fun c => (3388604417-1+2*2^9*c.k,103313255409091+c.lower,103313637658284+c.upper)) = pointBounds25823 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000181
