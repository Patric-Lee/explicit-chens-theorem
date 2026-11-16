import PlattAssemblyKernel
import PlattCertificates.Count131072.C013808
import PlattCertificates.Count131072.C013809
import PlattCertificates.Count131072.C013810
import PlattCertificates.Count131072.C013811
import PlattCertificates.Count131072.C013812
import PlattCertificates.Count131072.C013813
import PlattCertificates.Count131072.C013814
import PlattCertificates.Count131072.C013815
import PlattCertificates.Count131072.C013816
import PlattCertificates.Count131072.C013817
import PlattCertificates.Count131072.C013818
import PlattCertificates.Count131072.C013819
import PlattCertificates.Count131072.C013820
import PlattCertificates.Count131072.C013821
import PlattCertificates.Count131072.C013822
import PlattCertificates.Count131072.C013823
import PlattCertificates.Count131072.C013824
import PlattCertificates.Count131072.C013825
import PlattCertificates.Count131072.C013826
import PlattCertificates.Count131072.C013827
import PlattCertificates.Count131072.C013828
import PlattCertificates.Count131072.C013829
import PlattCertificates.Count131072.C013830
import PlattCertificates.Count131072.C013831
import PlattCertificates.Count131072.C013832
import PlattCertificates.Count131072.C013833
import PlattCertificates.Count131072.C013834
import PlattCertificates.Count131072.C013835
import PlattCertificates.Count131072.C013836
import PlattCertificates.Count131072.C013837
import PlattCertificates.Count131072.C013838
import PlattCertificates.Count131072.C013839
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000119
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts13808 : List PrefixCut := [⟨27,200190180,200190321⟩,
⟨83,612044811,612045245⟩,
⟨128,945057193,945057862⟩]
theorem checked13808 : checkPrefixCuts (2^48) 1813774337 9 Manual.Count131072.C013808.packed 128 cuts13808 = true := by
 decide +kernel
def pointBounds13808 : List (Nat × Nat × Nat) := [(1813801984,95180265578881,95180642870466),(1813859328,95180677433512,95181054725390)]
theorem point_links_checked13808 : (cuts13808.take 2).map (fun c => (1813774337-1+2*2^9*c.k,95180065388701+c.lower,95180442680145+c.upper)) = pointBounds13808 := by
 decide +kernel
def cuts13809 : List PrefixCut := [⟨11,84725924,84725983⟩,
⟨67,498261310,498261658⟩,
⟨123,913335306,913335944⟩,
⟨128,952592094,952592758⟩]
theorem checked13809 : checkPrefixCuts (2^48) 1813905409 9 Manual.Count131072.C013809.packed 128 cuts13809 = true := by
 decide +kernel
def pointBounds13809 : List (Nat × Nat × Nat) := [(1813916672,95181095171818,95181472463990),(1813974016,95181508707204,95181885999665),(1814031360,95181923781200,95182301073951)]
theorem point_links_checked13809 : (cuts13809.take 3).map (fun c => (1813905409-1+2*2^9*c.k,95181010445894+c.lower,95181387738007+c.upper)) = pointBounds13809 := by
 decide +kernel
def cuts13810 : List PrefixCut := [⟨51,383407122,383407384⟩,
⟨107,792558837,792559385⟩,
⟨128,946006776,946007431⟩]
theorem checked13810 : checkPrefixCuts (2^48) 1814036481 9 Manual.Count131072.C013810.packed 128 cuts13810 = true := by
 decide +kernel
def pointBounds13810 : List (Nat × Nat × Nat) := [(1814088704,95182346445110,95182723738149),(1814146048,95182755596825,95183132890150)]
theorem point_links_checked13810 : (cuts13810.take 2).map (fun c => (1814036481-1+2*2^9*c.k,95181963037988+c.lower,95182340330765+c.upper)) = pointBounds13810 := by
 decide +kernel
def cuts13811 : List PrefixCut := [⟨35,270120022,270120212⟩,
⟨91,680021633,680022108⟩,
⟨128,959901665,959902333⟩]
theorem checked13811 : checkPrefixCuts (2^48) 1814167553 9 Manual.Count131072.C013811.packed 128 cuts13811 = true := by
 decide +kernel
def pointBounds13811 : List (Nat × Nat × Nat) := [(1814203392,95183179164786,95183556458408),(1814260736,95183589066397,95183966360304)]
theorem point_links_checked13811 : (cuts13811.take 2).map (fun c => (1814167553-1+2*2^9*c.k,95182909044764+c.lower,95183286338196+c.upper)) = pointBounds13811 := by
 decide +kernel
def cuts13812 : List PrefixCut := [⟨19,142575234,142575331⟩,
⟨75,560673309,560673698⟩,
⟨128,954557682,954558347⟩]
theorem checked13812 : checkPrefixCuts (2^48) 1814298625 9 Manual.Count131072.C013812.packed 128 cuts13812 = true := by
 decide +kernel
def pointBounds13812 : List (Nat × Nat × Nat) := [(1814318080,95184011521663,95184388815860),(1814375424,95184429619738,95184806914227)]
theorem point_links_checked13812 : (cuts13812.take 2).map (fun c => (1814298625-1+2*2^9*c.k,95183868946429+c.lower,95184246240529+c.upper)) = pointBounds13812 := by
 decide +kernel
def cuts13813 : List PrefixCut := [⟨3,22183761,22183776⟩,
⟨59,435446307,435446610⟩,
⟨115,866069672,866070276⟩,
⟨128,965191787,965192461⟩]
theorem checked13813 : checkPrefixCuts (2^48) 1814429697 9 Manual.Count131072.C013813.packed 128 cuts13813 = true := by
 decide +kernel
def pointBounds13813 : List (Nat × Nat × Nat) := [(1814432768,95184845687872,95185222982652),(1814490112,95185258950418,95185636245486),(1814547456,95185689573783,95186066869152)]
theorem point_links_checked13813 : (cuts13813.take 3).map (fun c => (1814429697-1+2*2^9*c.k,95184823504111+c.lower,95185200798876+c.upper)) = pointBounds13813 := by
 decide +kernel
def cuts13814 : List PrefixCut := [⟨43,322335645,322335871⟩,
⟨99,734007881,734008392⟩,
⟨128,952247871,952248535⟩]
theorem checked13814 : checkPrefixCuts (2^48) 1814560769 9 Manual.Count131072.C013814.packed 128 cuts13814 = true := by
 decide +kernel
def pointBounds13814 : List (Nat × Nat × Nat) := [(1814604800,95186111031543,95186488327208),(1814662144,95186522703779,95186899999729)]
theorem point_links_checked13814 : (cuts13814.take 2).map (fun c => (1814560769-1+2*2^9*c.k,95185788695898+c.lower,95186165991337+c.upper)) = pointBounds13814 := by
 decide +kernel
def cuts13815 : List PrefixCut := [⟨27,202725824,202725967⟩,
⟨83,612976234,612976665⟩,
⟨128,946750719,946751382⟩]
theorem checked13815 : checkPrefixCuts (2^48) 1814691841 9 Manual.Count131072.C013815.packed 128 cuts13815 = true := by
 decide +kernel
def pointBounds13815 : List (Nat × Nat × Nat) := [(1814719488,95186943669593,95187320965839),(1814776832,95187353920003,95187731216537)]
theorem point_links_checked13815 : (cuts13815.take 2).map (fun c => (1814691841-1+2*2^9*c.k,95186740943769+c.lower,95187118239872+c.upper)) = pointBounds13815 := by
 decide +kernel
def cuts13816 : List PrefixCut := [⟨11,79719970,79720027⟩,
⟨67,495993056,495993399⟩,
⟨123,913493795,913494430⟩,
⟨128,950869697,950870359⟩]
theorem checked13816 : checkPrefixCuts (2^48) 1814822913 9 Manual.Count131072.C013816.packed 128 cuts13816 = true := by
 decide +kernel
def pointBounds13816 : List (Nat × Nat × Nat) := [(1814834176,95187767414458,95188144711281),(1814891520,95188183687544,95188560984653),(1814948864,95188601188283,95188978485684)]
theorem point_links_checked13816 : (cuts13816.take 3).map (fun c => (1814822913-1+2*2^9*c.k,95187687694488+c.lower,95188064991254+c.upper)) = pointBounds13816 := by
 decide +kernel
def cuts13817 : List PrefixCut := [⟨51,373287894,373288152⟩,
⟨107,787970723,787971275⟩,
⟨128,945528171,945528832⟩]
theorem checked13817 : checkPrefixCuts (2^48) 1814953985 9 Manual.Count131072.C013817.packed 128 cuts13817 = true := by
 decide +kernel
def pointBounds13817 : List (Nat × Nat × Nat) := [(1815006208,95189011852079,95189389149765),(1815063552,95189426534908,95189803832888)]
theorem point_links_checked13817 : (cuts13817.take 2).map (fun c => (1814953985-1+2*2^9*c.k,95188638564185+c.lower,95189015861613+c.upper)) = pointBounds13817 := by
 decide +kernel
def cuts13818 : List PrefixCut := [⟨35,265796487,265796672⟩,
⟨91,684640036,684640514⟩,
⟨128,956160104,956160772⟩]
theorem checked13818 : checkPrefixCuts (2^48) 1815085057 9 Manual.Count131072.C013818.packed 128 cuts13818 = true := by
 decide +kernel
def pointBounds13818 : List (Nat × Nat × Nat) := [(1815120896,95189849888843,95190227187117),(1815178240,95190268732392,95190646030959)]
theorem point_links_checked13818 : (cuts13818.take 2).map (fun c => (1815085057-1+2*2^9*c.k,95189584092356+c.lower,95189961390445+c.upper)) = pointBounds13818 := by
 decide +kernel
def cuts13819 : List PrefixCut := [⟨19,137851273,137851370⟩,
⟨75,557133557,557133951⟩,
⟨128,952524411,952525081⟩]
theorem checked13819 : checkPrefixCuts (2^48) 1815216129 9 Manual.Count131072.C013819.packed 128 cuts13819 = true := by
 decide +kernel
def pointBounds13819 : List (Nat × Nat × Nat) := [(1815235584,95190678103733,95191055402587),(1815292928,95191097386017,95191474685168)]
theorem point_links_checked13819 : (cuts13819.take 2).map (fun c => (1815216129-1+2*2^9*c.k,95190540252460+c.lower,95190917551217+c.upper)) = pointBounds13819 := by
 decide +kernel
def cuts13820 : List PrefixCut := [⟨3,24963498,24963516⟩,
⟨59,442358623,442358929⟩,
⟨115,868423170,868423771⟩,
⟨128,964859480,964860148⟩]
theorem checked13820 : checkPrefixCuts (2^48) 1815347201 9 Manual.Count131072.C013820.packed 128 cuts13820 = true := by
 decide +kernel
def pointBounds13820 : List (Nat × Nat × Nat) := [(1815350272,95191517740369,95191895039814),(1815407616,95191935135494,95192312435227),(1815464960,95192361200041,95192738500069)]
theorem point_links_checked13820 : (cuts13820.take 3).map (fun c => (1815347201-1+2*2^9*c.k,95191492776871+c.lower,95191870076298+c.upper)) = pointBounds13820 := by
 decide +kernel
def cuts13821 : List PrefixCut := [⟨43,317831689,317831913⟩,
⟨99,739528249,739528770⟩,
⟨128,950371491,950372157⟩]
theorem checked13821 : checkPrefixCuts (2^48) 1815478273 9 Manual.Count131072.C013821.packed 128 cuts13821 = true := by
 decide +kernel
def pointBounds13821 : List (Nat × Nat × Nat) := [(1815522304,95192775468040,95193152768359),(1815579648,95193197164600,95193574465216)]
theorem point_links_checked13821 : (cuts13821.take 2).map (fun c => (1815478273-1+2*2^9*c.k,95192457636351+c.lower,95192834936446+c.upper)) = pointBounds13821 := by
 decide +kernel
def cuts13822 : List PrefixCut := [⟨27,205568923,205569066⟩,
⟨83,620572834,620573269⟩,
⟨128,948752876,948753541⟩]
theorem checked13822 : checkPrefixCuts (2^48) 1815609345 9 Manual.Count131072.C013822.packed 128 cuts13822 = true := by
 decide +kernel
def pointBounds13822 : List (Nat × Nat × Nat) := [(1815636992,95193613576765,95193990877669),(1815694336,95194028580676,95194405881872)]
theorem point_links_checked13822 : (cuts13822.take 2).map (fun c => (1815609345-1+2*2^9*c.k,95193408007842+c.lower,95193785308603+c.upper)) = pointBounds13822 := by
 decide +kernel
def cuts13823 : List PrefixCut := [⟨11,90376000,90376062⟩,
⟨67,495122549,495122898⟩,
⟨123,915822595,915823234⟩,
⟨128,954574689,954575355⟩]
theorem checked13823 : checkPrefixCuts (2^48) 1815740417 9 Manual.Count131072.C013823.packed 128 cuts13823 = true := by
 decide +kernel
def pointBounds13823 : List (Nat × Nat × Nat) := [(1815751680,95194447136718,95194824438206),(1815809024,95194851883267,95195229185042),(1815866368,95195272583313,95195649885378)]
theorem point_links_checked13823 : (cuts13823.take 3).map (fun c => (1815740417-1+2*2^9*c.k,95194356760718+c.lower,95194734062144+c.upper)) = pointBounds13823 := by
 decide +kernel
def cuts13824 : List PrefixCut := [⟨51,378989502,378989765⟩,
⟨107,792377840,792378391⟩,
⟨128,954505607,954506272⟩]
theorem checked13824 : checkPrefixCuts (2^48) 1815871489 9 Manual.Count131072.C013824.packed 128 cuts13824 = true := by
 decide +kernel
def pointBounds13824 : List (Nat × Nat × Nat) := [(1815923712,95195690324909,95196067627264),(1815981056,95196103713247,95196481015890)]
theorem point_links_checked13824 : (cuts13824.take 2).map (fun c => (1815871489-1+2*2^9*c.k,95195311335407+c.lower,95195688637499+c.upper)) = pointBounds13824 := by
 decide +kernel
def cuts13825 : List PrefixCut := [⟨35,258842383,258842566⟩,
⟨91,679954114,679954588⟩,
⟨128,968850603,968851275⟩]
theorem checked13825 : checkPrefixCuts (2^48) 1816002561 9 Manual.Count131072.C013825.packed 128 cuts13825 = true := by
 decide +kernel
def pointBounds13825 : List (Nat × Nat × Nat) := [(1816038400,95196524683397,95196901986337),(1816095744,95196945795128,95197323098359)]
theorem point_links_checked13825 : (cuts13825.take 2).map (fun c => (1816002561-1+2*2^9*c.k,95196265841014+c.lower,95196643143771+c.upper)) = pointBounds13825 := by
 decide +kernel
def cuts13826 : List PrefixCut := [⟨19,135921784,135921880⟩,
⟨75,548173033,548173417⟩,
⟨128,939489648,939490305⟩]
theorem checked13826 : checkPrefixCuts (2^48) 1816133633 9 Manual.Count131072.C013826.packed 128 cuts13826 = true := by
 decide +kernel
def pointBounds13826 : List (Nat × Nat × Nat) := [(1816153088,95197370613401,95197747916926),(1816210432,95197782864650,95198160168463)]
theorem point_links_checked13826 : (cuts13826.take 2).map (fun c => (1816133633-1+2*2^9*c.k,95197234691617+c.lower,95197611995046+c.upper)) = pointBounds13826 := by
 decide +kernel
def cuts13827 : List PrefixCut := [⟨3,23556117,23556133⟩,
⟨59,440430515,440430823⟩,
⟨115,849698299,849698892⟩,
⟨128,949495112,949495774⟩]
theorem checked13827 : checkPrefixCuts (2^48) 1816264705 9 Manual.Count131072.C013827.packed 128 cuts13827 = true := by
 decide +kernel
def pointBounds13827 : List (Nat × Nat × Nat) := [(1816267776,95198197737382,95198575041484),(1816325120,95198614611780,95198991916174),(1816382464,95199023879564,95199401184243)]
theorem point_links_checked13827 : (cuts13827.take 3).map (fun c => (1816264705-1+2*2^9*c.k,95198174181265+c.lower,95198551485351+c.upper)) = pointBounds13827 := by
 decide +kernel
def cuts13828 : List PrefixCut := [⟨43,320615355,320615578⟩,
⟨99,735590686,735591199⟩,
⟨128,952990455,952991115⟩]
theorem checked13828 : checkPrefixCuts (2^48) 1816395777 9 Manual.Count131072.C013828.packed 128 cuts13828 = true := by
 decide +kernel
def pointBounds13828 : List (Nat × Nat × Nat) := [(1816439808,95199444291732,95199821596703),(1816497152,95199859267063,95200236572324)]
theorem point_links_checked13828 : (cuts13828.take 2).map (fun c => (1816395777-1+2*2^9*c.k,95199123676377+c.lower,95199500981125+c.upper)) = pointBounds13828 := by
 decide +kernel
def cuts13829 : List PrefixCut := [⟨27,202521039,202521184⟩,
⟨83,620569197,620569639⟩,
⟨128,955710869,955711543⟩]
theorem checked13829 : checkPrefixCuts (2^48) 1816526849 9 Manual.Count131072.C013829.packed 128 cuts13829 = true := by
 decide +kernel
def pointBounds13829 : List (Nat × Nat × Nat) := [(1816554496,95200279187871,95200656493424),(1816611840,95200697236029,95201074541879)]
theorem point_links_checked13829 : (cuts13829.take 2).map (fun c => (1816526849-1+2*2^9*c.k,95200076666832+c.lower,95200453972240+c.upper)) = pointBounds13829 := by
 decide +kernel
def cuts13830 : List PrefixCut := [⟨11,84752487,84752544⟩,
⟨67,499365615,499365962⟩,
⟨123,913810734,913811374⟩,
⟨128,950684093,950684759⟩]
theorem checked13830 : checkPrefixCuts (2^48) 1816657921 9 Manual.Count131072.C013830.packed 128 cuts13830 = true := by
 decide +kernel
def pointBounds13830 : List (Nat × Nat × Nat) := [(1816669184,95201117130188,95201494436327),(1816726528,95201531743316,95201909049745),(1816783872,95201946188435,95202323495157)]
theorem point_links_checked13830 : (cuts13830.take 3).map (fun c => (1816657921-1+2*2^9*c.k,95201032377701+c.lower,95201409683783+c.upper)) = pointBounds13830 := by
 decide +kernel
def cuts13831 : List PrefixCut := [⟨51,379262850,379263112⟩,
⟨107,801118062,801118619⟩,
⟨128,956812263,956812931⟩]
theorem checked13831 : checkPrefixCuts (2^48) 1816788993 9 Manual.Count131072.C013831.packed 128 cuts13831 = true := by
 decide +kernel
def pointBounds13831 : List (Nat × Nat × Nat) := [(1816841216,95202362324644,95202739631654),(1816898560,95202784179856,95203161487161)]
theorem point_links_checked13831 : (cuts13831.take 2).map (fun c => (1816788993-1+2*2^9*c.k,95201983061794+c.lower,95202360368542+c.upper)) = pointBounds13831 := by
 decide +kernel
def cuts13832 : List PrefixCut := [⟨35,255148573,255148753⟩,
⟨91,667682343,667682815⟩,
⟨128,943420596,943421263⟩]
theorem checked13832 : checkPrefixCuts (2^48) 1816920065 9 Manual.Count131072.C013832.packed 128 cuts13832 = true := by
 decide +kernel
def pointBounds13832 : List (Nat × Nat × Nat) := [(1816955904,95203195022630,95203572330226),(1817013248,95203607556400,95203984864288)]
theorem point_links_checked13832 : (cuts13832.take 2).map (fun c => (1816920065-1+2*2^9*c.k,95202939874057+c.lower,95203317181473+c.upper)) = pointBounds13832 := by
 decide +kernel
def cuts13833 : List PrefixCut := [⟨19,140655268,140655361⟩,
⟨75,544333585,544333961⟩,
⟨128,944127072,944127727⟩]
theorem checked13833 : checkPrefixCuts (2^48) 1817051137 9 Manual.Count131072.C013833.packed 128 cuts13833 = true := by
 decide +kernel
def pointBounds13833 : List (Nat × Nat × Nat) := [(1817070592,95204023949921,95204401258097),(1817127936,95204427628238,95204804936697)]
theorem point_links_checked13833 : (cuts13833.take 2).map (fun c => (1817051137-1+2*2^9*c.k,95203883294653+c.lower,95204260602736+c.upper)) = pointBounds13833 := by
 decide +kernel
def cuts13834 : List PrefixCut := [⟨3,21530574,21530589⟩,
⟨59,436645586,436645894⟩,
⟨115,852057177,852057773⟩,
⟨128,947776559,947777223⟩]
theorem checked13834 : checkPrefixCuts (2^48) 1817182209 9 Manual.Count131072.C013834.packed 128 cuts13834 = true := by
 decide +kernel
def pointBounds13834 : List (Nat × Nat × Nat) := [(1817185280,95204848952299,95205226261052),(1817242624,95205264067311,95205641376357),(1817299968,95205679478902,95206056788236)]
theorem point_links_checked13834 : (cuts13834.take 3).map (fun c => (1817182209-1+2*2^9*c.k,95204827421725+c.lower,95205204730463+c.upper)) = pointBounds13834 := by
 decide +kernel
def cuts13835 : List PrefixCut := [⟨43,326803727,326803955⟩,
⟨99,739556176,739556693⟩,
⟨128,955762059,955762729⟩]
theorem checked13835 : checkPrefixCuts (2^48) 1817313281 9 Manual.Count131072.C013835.packed 128 cuts13835 = true := by
 decide +kernel
def pointBounds13835 : List (Nat × Nat × Nat) := [(1817357312,95206102002011,95206479311641),(1817414656,95206514754460,95206892064379)]
theorem point_links_checked13835 : (cuts13835.take 2).map (fun c => (1817313281-1+2*2^9*c.k,95205775198284+c.lower,95206152507686+c.upper)) = pointBounds13835 := by
 decide +kernel
def cuts13836 : List PrefixCut := [⟨27,199166452,199166590⟩,
⟨83,626295709,626296144⟩,
⟨128,957706361,957707023⟩]
theorem checked13836 : checkPrefixCuts (2^48) 1817444353 9 Manual.Count131072.C013836.packed 128 cuts13836 = true := by
 decide +kernel
def pointBounds13836 : List (Nat × Nat × Nat) := [(1817472000,95206930126795,95207307437005),(1817529344,95207357256052,95207734566559)]
theorem point_links_checked13836 : (cuts13836.take 2).map (fun c => (1817444353-1+2*2^9*c.k,95206730960343+c.lower,95207108270415+c.upper)) = pointBounds13836 := by
 decide +kernel
def cuts13837 : List PrefixCut := [⟨11,79289524,79289577⟩,
⟨67,502984883,502985230⟩,
⟨123,922485804,922486445⟩,
⟨128,957172626,957173292⟩]
theorem checked13837 : checkPrefixCuts (2^48) 1817575425 9 Manual.Count131072.C013837.packed 128 cuts13837 = true := by
 decide +kernel
def pointBounds13837 : List (Nat × Nat × Nat) := [(1817586688,95207767956228,95208145267015),(1817644032,95208191651587,95208568962668),(1817701376,95208611152508,95208988463883)]
theorem point_links_checked13837 : (cuts13837.take 3).map (fun c => (1817575425-1+2*2^9*c.k,95207688666704+c.lower,95208065977438+c.upper)) = pointBounds13837 := by
 decide +kernel
def cuts13838 : List PrefixCut := [⟨51,376748726,376748987⟩,
⟨107,794984518,794985072⟩,
⟨128,948122678,948123341⟩]
theorem checked13838 : checkPrefixCuts (2^48) 1817706497 9 Manual.Count131072.C013838.packed 128 cuts13838 = true := by
 decide +kernel
def pointBounds13838 : List (Nat × Nat × Nat) := [(1817758720,95209022588056,95209399899717),(1817816064,95209440823848,95209818135802)]
theorem point_links_checked13838 : (cuts13838.take 2).map (fun c => (1817706497-1+2*2^9*c.k,95208645839330+c.lower,95209023150730+c.upper)) = pointBounds13838 := by
 decide +kernel
def cuts13839 : List PrefixCut := [⟨35,259510132,259510311⟩,
⟨91,673229252,673229716⟩,
⟨128,954711933,954712592⟩]
theorem checked13839 : checkPrefixCuts (2^48) 1817837569 9 Manual.Count131072.C013839.packed 128 cuts13839 = true := by
 decide +kernel
def pointBounds13839 : List (Nat × Nat × Nat) := [(1817873408,95209853472140,95210230784382),(1817930752,95210267191260,95210644503787)]
theorem point_links_checked13839 : (cuts13839.take 2).map (fun c => (1817837569-1+2*2^9*c.k,95209593962008+c.lower,95209971274071+c.upper)) = pointBounds13839 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000119
