import PlattAssemblyKernel
import PlattCertificates.Count131072.C014800
import PlattCertificates.Count131072.C014801
import PlattCertificates.Count131072.C014802
import PlattCertificates.Count131072.C014803
import PlattCertificates.Count131072.C014804
import PlattCertificates.Count131072.C014805
import PlattCertificates.Count131072.C014806
import PlattCertificates.Count131072.C014807
import PlattCertificates.Count131072.C014808
import PlattCertificates.Count131072.C014809
import PlattCertificates.Count131072.C014810
import PlattCertificates.Count131072.C014811
import PlattCertificates.Count131072.C014812
import PlattCertificates.Count131072.C014813
import PlattCertificates.Count131072.C014814
import PlattCertificates.Count131072.C014815
import PlattCertificates.Count131072.C014816
import PlattCertificates.Count131072.C014817
import PlattCertificates.Count131072.C014818
import PlattCertificates.Count131072.C014819
import PlattCertificates.Count131072.C014820
import PlattCertificates.Count131072.C014821
import PlattCertificates.Count131072.C014822
import PlattCertificates.Count131072.C014823
import PlattCertificates.Count131072.C014824
import PlattCertificates.Count131072.C014825
import PlattCertificates.Count131072.C014826
import PlattCertificates.Count131072.C014827
import PlattCertificates.Count131072.C014828
import PlattCertificates.Count131072.C014829
import PlattCertificates.Count131072.C014830
import PlattCertificates.Count131072.C014831
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000150
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts14800 : List PrefixCut := [⟨58,397198700,397198970⟩,
⟨118,808140986,808141530⟩,
⟨128,877498890,877499480⟩]
theorem checked14800 : checkPrefixCuts (2^48) 1943797761 9 Manual.Count131072.C014800.packed 128 cuts14800 = true := by
 decide +kernel
def pointBounds14800 : List (Nat × Nat × Nat) := [(1943857152,96092888265784,96093266182174),(1943918592,96093299208070,96093677124734)]
theorem point_links_checked14800 : (cuts14800.take 2).map (fun c => (1943797761-1+2*2^9*c.k,96092491067084+c.lower,96092868983204+c.upper)) = pointBounds14800 := by
 decide +kernel
def cuts14801 : List PrefixCut := [⟨50,343164165,343164393⟩,
⟨110,762188837,762189343⟩,
⟨128,890470848,890471441⟩]
theorem checked14801 : checkPrefixCuts (2^48) 1943928833 9 Manual.Count131072.C014801.packed 128 cuts14801 = true := by
 decide +kernel
def pointBounds14801 : List (Nat × Nat × Nat) := [(1943980032,96093711730139,96094089647077),(1944041472,96094130754811,96094508672027)]
theorem point_links_checked14801 : (cuts14801.take 2).map (fun c => (1943928833-1+2*2^9*c.k,96093368565974+c.lower,96093746482684+c.upper)) = pointBounds14801 := by
 decide +kernel
def cuts14802 : List PrefixCut := [⟨42,287399294,287399484⟩,
⟨102,715808258,715808728⟩,
⟨128,898373795,898374384⟩]
theorem checked14802 : checkPrefixCuts (2^48) 1944059905 9 Manual.Count131072.C014802.packed 128 cuts14802 = true := by
 decide +kernel
def pointBounds14802 : List (Nat × Nat × Nat) := [(1944102912,96094546436116,96094924353609),(1944164352,96094974845080,96095352762853)]
theorem point_links_checked14802 : (cuts14802.take 2).map (fun c => (1944059905-1+2*2^9*c.k,96094259036822+c.lower,96094636954125+c.upper)) = pointBounds14802 := by
 decide +kernel
def cuts14803 : List PrefixCut := [⟨34,234826798,234826957⟩,
⟨94,648731350,648731790⟩,
⟨128,887744869,887745469⟩]
theorem checked14803 : checkPrefixCuts (2^48) 1944190977 9 Manual.Count131072.C014803.packed 128 cuts14803 = true := by
 decide +kernel
def pointBounds14803 : List (Nat × Nat × Nat) := [(1944225792,96095392237415,96095770155466),(1944287232,96095806141967,96096184060299)]
theorem point_links_checked14803 : (cuts14803.take 2).map (fun c => (1944190977-1+2*2^9*c.k,96095157410617+c.lower,96095535328509+c.upper)) = pointBounds14803 := by
 decide +kernel
def cuts14804 : List PrefixCut := [⟨26,175891445,175891564⟩,
⟨86,601206146,601206552⟩,
⟨128,894923104,894923705⟩]
theorem checked14804 : checkPrefixCuts (2^48) 1944322049 9 Manual.Count131072.C014804.packed 128 cuts14804 = true := by
 decide +kernel
def pointBounds14804 : List (Nat × Nat × Nat) := [(1944348672,96096221046931,96096598965542),(1944410112,96096646361632,96097024280530)]
theorem point_links_checked14804 : (cuts14804.take 2).map (fun c => (1944322049-1+2*2^9*c.k,96096045155486+c.lower,96096423073978+c.upper)) = pointBounds14804 := by
 decide +kernel
def cuts14805 : List PrefixCut := [⟨18,121451291,121451371⟩,
⟨78,533856025,533856379⟩,
⟨128,871557730,871558316⟩]
theorem checked14805 : checkPrefixCuts (2^48) 1944453121 9 Manual.Count131072.C014805.packed 128 cuts14805 = true := by
 decide +kernel
def pointBounds14805 : List (Nat × Nat × Nat) := [(1944471552,96097061529881,96097439449054),(1944532992,96097473934615,96097851854062)]
theorem point_links_checked14805 : (cuts14805.take 2).map (fun c => (1944453121-1+2*2^9*c.k,96096940078590+c.lower,96097317997683+c.upper)) = pointBounds14805 := by
 decide +kernel
def cuts14806 : List PrefixCut := [⟨10,69623657,69623705⟩,
⟨70,488226355,488226689⟩,
⟨128,888289279,888289879⟩]
theorem checked14806 : checkPrefixCuts (2^48) 1944584193 9 Manual.Count131072.C014806.packed 128 cuts14806 = true := by
 decide +kernel
def pointBounds14806 : List (Nat × Nat × Nat) := [(1944594432,96097881259977,96098259179704),(1944655872,96098299862675,96098677782688)]
theorem point_links_checked14806 : (cuts14806.take 2).map (fun c => (1944584193-1+2*2^9*c.k,96097811636320+c.lower,96098189555999+c.upper)) = pointBounds14806 := by
 decide +kernel
def cuts14807 : List PrefixCut := [⟨2,12736968,12736977⟩,
⟨62,426102743,426103030⟩,
⟨122,843218443,843219014⟩,
⟨128,881137396,881137992⟩]
theorem checked14807 : checkPrefixCuts (2^48) 1944715265 9 Manual.Count131072.C014807.packed 128 cuts14807 = true := by
 decide +kernel
def pointBounds14807 : List (Nat × Nat × Nat) := [(1944717312,96098712662567,96099090582855),(1944778752,96099126028342,96099503948908),(1944840192,96099543144042,96099921064892)]
theorem point_links_checked14807 : (cuts14807.take 3).map (fun c => (1944715265-1+2*2^9*c.k,96098699925599+c.lower,96099077845878+c.upper)) = pointBounds14807 := by
 decide +kernel
def cuts14808 : List PrefixCut := [⟨54,384104190,384104448⟩,
⟨114,804232700,804233240⟩,
⟨128,899892214,899892819⟩]
theorem checked14808 : checkPrefixCuts (2^48) 1944846337 9 Manual.Count131072.C014808.packed 128 cuts14808 = true := by
 decide +kernel
def pointBounds14808 : List (Nat × Nat × Nat) := [(1944901632,96099965167185,96100343088318),(1944963072,96100385295695,96100763217110)]
theorem point_links_checked14808 : (cuts14808.take 2).map (fun c => (1944846337-1+2*2^9*c.k,96099581062995+c.lower,96099958983870+c.upper)) = pointBounds14808 := by
 decide +kernel
def cuts14809 : List PrefixCut := [⟨46,319679993,319680209⟩,
⟨106,729217935,729218427⟩,
⟨128,882610460,882611056⟩]
theorem checked14809 : checkPrefixCuts (2^48) 1944977409 9 Manual.Count131072.C014809.packed 128 cuts14809 = true := by
 decide +kernel
def pointBounds14809 : List (Nat × Nat × Nat) := [(1945024512,96100800635202,96101178556898),(1945085952,96101210173144,96101588095116)]
theorem point_links_checked14809 : (cuts14809.take 2).map (fun c => (1944977409-1+2*2^9*c.k,96100480955209+c.lower,96100858876689+c.upper)) = pointBounds14809 := by
 decide +kernel
def cuts14810 : List PrefixCut := [⟨38,257000799,257000971⟩,
⟨98,667959885,667960341⟩,
⟨128,879946113,879946711⟩]
theorem checked14810 : checkPrefixCuts (2^48) 1945108481 9 Manual.Count131072.C014810.packed 128 cuts14810 = true := by
 decide +kernel
def pointBounds14810 : List (Nat × Nat × Nat) := [(1945147392,96101620566468,96101998488716),(1945208832,96102031525554,96102409448086)]
theorem point_links_checked14810 : (cuts14810.take 2).map (fun c => (1945108481-1+2*2^9*c.k,96101363565669+c.lower,96101741487745+c.upper)) = pointBounds14810 := by
 decide +kernel
def cuts14811 : List PrefixCut := [⟨30,208654824,208654963⟩,
⟨90,628414313,628414741⟩,
⟨128,889002904,889003507⟩]
theorem checked14811 : checkPrefixCuts (2^48) 1945239553 9 Manual.Count131072.C014811.packed 128 cuts14811 = true := by
 decide +kernel
def pointBounds14811 : List (Nat × Nat × Nat) := [(1945270272,96102452166606,96102830089419),(1945331712,96102871926095,96103249849197)]
theorem point_links_checked14811 : (cuts14811.take 2).map (fun c => (1945239553-1+2*2^9*c.k,96102243511782+c.lower,96102621434456+c.upper)) = pointBounds14811 := by
 decide +kernel
def cuts14812 : List PrefixCut := [⟨22,153804148,153804251⟩,
⟨82,571945645,571946025⟩,
⟨128,894440925,894441518⟩]
theorem checked14812 : checkPrefixCuts (2^48) 1945370625 9 Manual.Count131072.C014812.packed 128 cuts14812 = true := by
 decide +kernel
def pointBounds14812 : List (Nat × Nat × Nat) := [(1945393152,96103286318834,96103664242214),(1945454592,96103704460331,96104082383988)]
theorem point_links_checked14812 : (cuts14812.take 2).map (fun c => (1945370625-1+2*2^9*c.k,96103132514686+c.lower,96103510437963+c.upper)) = pointBounds14812 := by
 decide +kernel
def cuts14813 : List PrefixCut := [⟨14,91871354,91871417⟩,
⟨74,506224774,506225115⟩,
⟨128,883095726,883096324⟩]
theorem checked14813 : checkPrefixCuts (2^48) 1945501697 9 Manual.Count131072.C014813.packed 128 cuts14813 = true := by
 decide +kernel
def pointBounds14813 : List (Nat × Nat × Nat) := [(1945516032,96104118826965,96104496750898),(1945577472,96104533180385,96104911104596)]
theorem point_links_checked14813 : (cuts14813.take 2).map (fun c => (1945501697-1+2*2^9*c.k,96104026955611+c.lower,96104404879481+c.upper)) = pointBounds14813 := by
 decide +kernel
def cuts14814 : List PrefixCut := [⟨6,43256293,43256322⟩,
⟨66,451073501,451073805⟩,
⟨126,863651846,863652427⟩,
⟨128,876960605,876961195⟩]
theorem checked14814 : checkPrefixCuts (2^48) 1945632769 9 Manual.Count131072.C014814.packed 128 cuts14814 = true := by
 decide +kernel
def pointBounds14814 : List (Nat × Nat × Nat) := [(1945638912,96104953307630,96105331232127),(1945700352,96105361124838,96105739049610),(1945761792,96105773703183,96106151628232)]
theorem point_links_checked14814 : (cuts14814.take 3).map (fun c => (1945632769-1+2*2^9*c.k,96104910051337+c.lower,96105287975805+c.upper)) = pointBounds14814 := by
 decide +kernel
def cuts14815 : List PrefixCut := [⟨58,405332108,405332377⟩,
⟨118,814412708,814413249⟩,
⟨128,885580998,885581587⟩]
theorem checked14815 : checkPrefixCuts (2^48) 1945763841 9 Manual.Count131072.C014815.packed 128 cuts14815 = true := by
 decide +kernel
def pointBounds14815 : List (Nat × Nat × Nat) := [(1945823232,96106192344050,96106570269377),(1945884672,96106601424650,96106979350249)]
theorem point_links_checked14815 : (cuts14815.take 2).map (fun c => (1945763841-1+2*2^9*c.k,96105787011942+c.lower,96106164937000+c.upper)) = pointBounds14815 := by
 decide +kernel
def cuts14816 : List PrefixCut := [⟨50,351641040,351641280⟩,
⟨110,758236667,758237183⟩,
⟨128,881760552,881761149⟩]
theorem checked14816 : checkPrefixCuts (2^48) 1945894913 9 Manual.Count131072.C014816.packed 128 cuts14816 = true := by
 decide +kernel
def pointBounds14816 : List (Nat × Nat × Nat) := [(1945946112,96107024233980,96107402159867),(1946007552,96107430829607,96107808755770)]
theorem point_links_checked14816 : (cuts14816.take 2).map (fun c => (1945894913-1+2*2^9*c.k,96106672592940+c.lower,96107050518587+c.upper)) = pointBounds14816 := by
 decide +kernel
def cuts14817 : List PrefixCut := [⟨42,296655124,296655321⟩,
⟨102,713928286,713928760⟩,
⟨128,886329757,886330347⟩]
theorem checked14817 : checkPrefixCuts (2^48) 1946025985 9 Manual.Count131072.C014817.packed 128 cuts14817 = true := by
 decide +kernel
def pointBounds14817 : List (Nat × Nat × Nat) := [(1946068992,96107851008616,96108228935057),(1946130432,96108268281778,96108646208496)]
theorem point_links_checked14817 : (cuts14817.take 2).map (fun c => (1946025985-1+2*2^9*c.k,96107554353492+c.lower,96107932279736+c.upper)) = pointBounds14817 := by
 decide +kernel
def cuts14818 : List PrefixCut := [⟨34,235312723,235312880⟩,
⟨94,654584231,654584667⟩,
⟨128,898707319,898707916⟩]
theorem checked14818 : checkPrefixCuts (2^48) 1946157057 9 Manual.Count131072.C014818.packed 128 cuts14818 = true := by
 decide +kernel
def pointBounds14818 : List (Nat × Nat × Nat) := [(1946191872,96108675995972,96109053922963),(1946253312,96109095267480,96109473194750)]
theorem point_links_checked14818 : (cuts14818.take 2).map (fun c => (1946157057-1+2*2^9*c.k,96108440683249+c.lower,96108818610083+c.upper)) = pointBounds14818 := by
 decide +kernel
def cuts14819 : List PrefixCut := [⟨26,179329292,179329412⟩,
⟨86,593512729,593513130⟩,
⟨128,887656069,887656662⟩]
theorem checked14819 : checkPrefixCuts (2^48) 1946288129 9 Manual.Count131072.C014819.packed 128 cuts14819 = true := by
 decide +kernel
def pointBounds14819 : List (Nat × Nat × Nat) := [(1946314752,96109518719860,96109896647411),(1946376192,96109932903297,96110310831129)]
theorem point_links_checked14819 : (cuts14819.take 2).map (fun c => (1946288129-1+2*2^9*c.k,96109339390568+c.lower,96109717317999+c.upper)) = pointBounds14819 := by
 decide +kernel
def cuts14820 : List PrefixCut := [⟨18,127402266,127402352⟩,
⟨78,545174651,545175021⟩,
⟨128,896272724,896273331⟩]
theorem checked14820 : checkPrefixCuts (2^48) 1946419201 9 Manual.Count131072.C014820.packed 128 cuts14820 = true := by
 decide +kernel
def pointBounds14820 : List (Nat × Nat × Nat) := [(1946437632,96110354448903,96110732377013),(1946499072,96110772221288,96111150149682)]
theorem point_links_checked14820 : (cuts14820.take 2).map (fun c => (1946419201-1+2*2^9*c.k,96110227046637+c.lower,96110604974661+c.upper)) = pointBounds14820 := by
 decide +kernel
def cuts14821 : List PrefixCut := [⟨10,67239717,67239761⟩,
⟨70,478768120,478768443⟩,
⟨128,880595912,880596501⟩]
theorem checked14821 : checkPrefixCuts (2^48) 1946550273 9 Manual.Count131072.C014821.packed 128 cuts14821 = true := by
 decide +kernel
def pointBounds14821 : List (Nat × Nat × Nat) := [(1946560512,96111190559078,96111568487753),(1946621952,96111602087481,96111980016435)]
theorem point_links_checked14821 : (cuts14821.take 2).map (fun c => (1946550273-1+2*2^9*c.k,96111123319361+c.lower,96111501247992+c.upper)) = pointBounds14821 := by
 decide +kernel
def cuts14822 : List PrefixCut := [⟨2,14892985,14892995⟩,
⟨62,428564235,428564524⟩,
⟨122,841644059,841644627⟩,
⟨128,882705536,882706129⟩]
theorem checked14822 : checkPrefixCuts (2^48) 1946681345 9 Manual.Count131072.C014822.packed 128 cuts14822 = true := by
 decide +kernel
def pointBounds14822 : List (Nat × Nat × Nat) := [(1946683392,96112018808258,96112396737488),(1946744832,96112432479508,96112810409017),(1946806272,96112845559332,96113223489120)]
theorem point_links_checked14822 : (cuts14822.take 3).map (fun c => (1946681345-1+2*2^9*c.k,96112003915273+c.lower,96112381844493+c.upper)) = pointBounds14822 := by
 decide +kernel
def cuts14823 : List PrefixCut := [⟨54,370993253,370993504⟩,
⟨114,786071118,786071641⟩,
⟨128,882212330,882212918⟩]
theorem checked14823 : checkPrefixCuts (2^48) 1946812417 9 Manual.Count131072.C014823.packed 128 cuts14823 = true := by
 decide +kernel
def pointBounds14823 : List (Nat × Nat × Nat) := [(1946867712,96113257614062,96113635544126),(1946929152,96113672691927,96114050622263)]
theorem point_links_checked14823 : (cuts14823.take 2).map (fun c => (1946812417-1+2*2^9*c.k,96112886620809+c.lower,96113264550622+c.upper)) = pointBounds14823 := by
 decide +kernel
def cuts14824 : List PrefixCut := [⟨46,320658424,320658636⟩,
⟨106,739757905,739758400⟩,
⟨128,891405350,891405949⟩]
theorem checked14824 : checkPrefixCuts (2^48) 1946943489 9 Manual.Count131072.C014824.packed 128 cuts14824 = true := by
 decide +kernel
def pointBounds14824 : List (Nat × Nat × Nat) := [(1946990592,96114089491563,96114467422176),(1947052032,96114508591044,96114886521940)]
theorem point_links_checked14824 : (cuts14824.take 2).map (fun c => (1946943489-1+2*2^9*c.k,96113768833139+c.lower,96114146763540+c.upper)) = pointBounds14824 := by
 decide +kernel
def cuts14825 : List PrefixCut := [⟨38,270619212,270619391⟩,
⟨98,686801168,686801626⟩,
⟨128,902476319,902476923⟩]
theorem checked14825 : checkPrefixCuts (2^48) 1947074561 9 Manual.Count131072.C014825.packed 128 cuts14825 = true := by
 decide +kernel
def pointBounds14825 : List (Nat × Nat × Nat) := [(1947113472,96114930857701,96115308788880),(1947174912,96115347039657,96115724971115)]
theorem point_links_checked14825 : (cuts14825.take 2).map (fun c => (1947074561-1+2*2^9*c.k,96114660238489+c.lower,96115038169489+c.upper)) = pointBounds14825 := by
 decide +kernel
def cuts14826 : List PrefixCut := [⟨30,203529358,203529494⟩,
⟨90,627490635,627491052⟩,
⟨128,886804266,886804860⟩]
theorem checked14826 : checkPrefixCuts (2^48) 1947205633 9 Manual.Count131072.C014826.packed 128 cuts14826 = true := by
 decide +kernel
def pointBounds14826 : List (Nat × Nat × Nat) := [(1947236352,96115766244166,96116144175906),(1947297792,96116190205443,96116568137464)]
theorem point_links_checked14826 : (cuts14826.take 2).map (fun c => (1947205633-1+2*2^9*c.k,96115562714808+c.lower,96115940646412+c.upper)) = pointBounds14826 := by
 decide +kernel
def cuts14827 : List PrefixCut := [⟨22,152492517,152492619⟩,
⟨82,568911067,568911449⟩,
⟨128,889924507,889925107⟩]
theorem checked14827 : checkPrefixCuts (2^48) 1947336705 9 Manual.Count131072.C014827.packed 128 cuts14827 = true := by
 decide +kernel
def pointBounds14827 : List (Nat × Nat × Nat) := [(1947359232,96116602011591,96116979943891),(1947420672,96117018430141,96117396362721)]
theorem point_links_checked14827 : (cuts14827.take 2).map (fun c => (1947336705-1+2*2^9*c.k,96116449519074+c.lower,96116827451272+c.upper)) = pointBounds14827 := by
 decide +kernel
def cuts14828 : List PrefixCut := [⟨14,95970073,95970137⟩,
⟨74,505713799,505714136⟩,
⟨128,880036407,880036998⟩]
theorem checked14828 : checkPrefixCuts (2^48) 1947467777 9 Manual.Count131072.C014828.packed 128 cuts14828 = true := by
 decide +kernel
def pointBounds14828 : List (Nat × Nat × Nat) := [(1947482112,96117435413654,96117813346516),(1947543552,96117845157380,96118223090515)]
theorem point_links_checked14828 : (cuts14828.take 2).map (fun c => (1947467777-1+2*2^9*c.k,96117339443581+c.lower,96117717376379+c.upper)) = pointBounds14828 := by
 decide +kernel
def cuts14829 : List PrefixCut := [⟨6,40755717,40755744⟩,
⟨66,458133242,458133551⟩,
⟨126,870873099,870873696⟩,
⟨128,884457454,884458059⟩]
theorem checked14829 : checkPrefixCuts (2^48) 1947598849 9 Manual.Count131072.C014829.packed 128 cuts14829 = true := by
 decide +kernel
def pointBounds14829 : List (Nat × Nat × Nat) := [(1947604992,96118260235705,96118638169121),(1947666432,96118677613230,96119055546928),(1947727872,96119090353087,96119468287073)]
theorem point_links_checked14829 : (cuts14829.take 3).map (fun c => (1947598849-1+2*2^9*c.k,96118219479988+c.lower,96118597413377+c.upper)) = pointBounds14829 := by
 decide +kernel
def cuts14830 : List PrefixCut := [⟨58,404778351,404778622⟩,
⟨118,825006622,825007176⟩,
⟨128,891767919,891768520⟩]
theorem checked14830 : checkPrefixCuts (2^48) 1947729921 9 Manual.Count131072.C014830.packed 128 cuts14830 = true := by
 decide +kernel
def pointBounds14830 : List (Nat × Nat × Nat) := [(1947789312,96119508715793,96119886650058),(1947850752,96119928944064,96120306878612)]
theorem point_links_checked14830 : (cuts14830.take 2).map (fun c => (1947729921-1+2*2^9*c.k,96119103937442+c.lower,96119481871436+c.upper)) = pointBounds14830 := by
 decide +kernel
def cuts14831 : List PrefixCut := [⟨50,346951012,346951244⟩,
⟨110,761517256,761517764⟩,
⟨128,888239863,888240455⟩]
theorem checked14831 : checkPrefixCuts (2^48) 1947860993 9 Manual.Count131072.C014831.packed 128 cuts14831 = true := by
 decide +kernel
def pointBounds14831 : List (Nat × Nat × Nat) := [(1947912192,96120342656373,96120720591200),(1947973632,96120757222617,96121135157720)]
theorem point_links_checked14831 : (cuts14831.take 2).map (fun c => (1947860993-1+2*2^9*c.k,96119995705361+c.lower,96120373639956+c.upper)) = pointBounds14831 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000150
