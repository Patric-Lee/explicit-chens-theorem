import PlattAssemblyKernel
import PlattCertificates.Count131072.C032880
import PlattCertificates.Count131072.C032881
import PlattCertificates.Count131072.C032882
import PlattCertificates.Count131072.C032883
import PlattCertificates.Count131072.C032884
import PlattCertificates.Count131072.C032885
import PlattCertificates.Count131072.C032886
import PlattCertificates.Count131072.C032887
import PlattCertificates.Count131072.C032888
import PlattCertificates.Count131072.C032889
import PlattCertificates.Count131072.C032890
import PlattCertificates.Count131072.C032891
import PlattCertificates.Count131072.C032892
import PlattCertificates.Count131072.C032893
import PlattCertificates.Count131072.C032894
import PlattCertificates.Count131072.C032895
import PlattCertificates.Count131072.C032896
import PlattCertificates.Count131072.C032897
import PlattCertificates.Count131072.C032898
import PlattCertificates.Count131072.C032899
import PlattCertificates.Count131072.C032900
import PlattCertificates.Count131072.C032901
import PlattCertificates.Count131072.C032902
import PlattCertificates.Count131072.C032903
import PlattCertificates.Count131072.C032904
import PlattCertificates.Count131072.C032905
import PlattCertificates.Count131072.C032906
import PlattCertificates.Count131072.C032907
import PlattCertificates.Count131072.C032908
import PlattCertificates.Count131072.C032909
import PlattCertificates.Count131072.C032910
import PlattCertificates.Count131072.C032911
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000090
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts32880 : List PrefixCut := [⟨10,59967547,59967586⟩,
⟨64,387859135,387859386⟩]
theorem checked32880 : checkPrefixCuts (2^48) 4313579521 10 Manual.Count131072.C032880.packed 64 cuts32880 = true := by
 decide +kernel
def pointBounds32880 : List (Nat × Nat × Nat) := [(4313600000,106392273883027,106392657865986)]
theorem point_links_checked32880 : (cuts32880.take 1).map (fun c => (4313579521-1+2*2^10*c.k,106392213915480+c.lower,106392597898400+c.upper)) = pointBounds32880 := by
 decide +kernel
def cuts32881 : List PrefixCut := [⟨12,68709338,68709383⟩,
⟨64,376820064,376820313⟩]
theorem checked32881 : checkPrefixCuts (2^48) 4313710593 10 Manual.Count131072.C032881.packed 64 cuts32881 = true := by
 decide +kernel
def pointBounds32881 : List (Nat × Nat × Nat) := [(4313735168,106392670483953,106393054467169)]
theorem point_links_checked32881 : (cuts32881.take 1).map (fun c => (4313710593-1+2*2^10*c.k,106392601774615+c.lower,106392985757786+c.upper)) = pointBounds32881 := by
 decide +kernel
def cuts32882 : List PrefixCut := [⟨14,82801013,82801065⟩,
⟨64,384051186,384051432⟩]
theorem checked32882 : checkPrefixCuts (2^48) 4313841665 10 Manual.Count131072.C032882.packed 64 cuts32882 = true := by
 decide +kernel
def pointBounds32882 : List (Nat × Nat × Nat) := [(4313870336,106393061395692,106393445379164)]
theorem point_links_checked32882 : (cuts32882.take 1).map (fun c => (4313841665-1+2*2^10*c.k,106392978594679+c.lower,106393362578099+c.upper)) = pointBounds32882 := by
 decide +kernel
def cuts32883 : List PrefixCut := [⟨16,97218052,97218116⟩,
⟨64,382799850,382800095⟩]
theorem checked32883 : checkPrefixCuts (2^48) 4313972737 10 Manual.Count131072.C032883.packed 64 cuts32883 = true := by
 decide +kernel
def pointBounds32883 : List (Nat × Nat × Nat) := [(4314005504,106393459863917,106393843847647)]
theorem point_links_checked32883 : (cuts32883.take 1).map (fun c => (4313972737-1+2*2^10*c.k,106393362645865+c.lower,106393746629531+c.upper)) = pointBounds32883 := by
 decide +kernel
def cuts32884 : List PrefixCut := [⟨18,111829924,111829995⟩,
⟨64,393423021,393423272⟩]
theorem checked32884 : checkPrefixCuts (2^48) 4314103809 10 Manual.Count131072.C032884.packed 64 cuts32884 = true := by
 decide +kernel
def pointBounds32884 : List (Nat × Nat × Nat) := [(4314140672,106393857275639,106394241259621)]
theorem point_links_checked32884 : (cuts32884.take 1).map (fun c => (4314103809-1+2*2^10*c.k,106393745445715+c.lower,106394129429626+c.upper)) = pointBounds32884 := by
 decide +kernel
def cuts32885 : List PrefixCut := [⟨20,120569038,120569116⟩,
⟨64,386234439,386234687⟩]
theorem checked32885 : checkPrefixCuts (2^48) 4314234881 10 Manual.Count131072.C032885.packed 64 cuts32885 = true := by
 decide +kernel
def pointBounds32885 : List (Nat × Nat × Nat) := [(4314275840,106394259437774,106394643422014)]
theorem point_links_checked32885 : (cuts32885.take 1).map (fun c => (4314234881-1+2*2^10*c.k,106394138868736+c.lower,106394522852898+c.upper)) = pointBounds32885 := by
 decide +kernel
def cuts32886 : List PrefixCut := [⟨22,132178213,132178299⟩,
⟨64,385048396,385048644⟩]
theorem checked32886 : checkPrefixCuts (2^48) 4314365953 10 Manual.Count131072.C032886.packed 64 cuts32886 = true := by
 decide +kernel
def pointBounds32886 : List (Nat × Nat × Nat) := [(4314411008,106394657281388,106395041265884)]
theorem point_links_checked32886 : (cuts32886.take 1).map (fun c => (4314365953-1+2*2^10*c.k,106394525103175+c.lower,106394909087585+c.upper)) = pointBounds32886 := by
 decide +kernel
def cuts32887 : List PrefixCut := [⟨24,145352399,145352493⟩,
⟨64,382883864,382884113⟩]
theorem checked32887 : checkPrefixCuts (2^48) 4314497025 10 Manual.Count131072.C032887.packed 64 cuts32887 = true := by
 decide +kernel
def pointBounds32887 : List (Nat × Nat × Nat) := [(4314546176,106395055503970,106395439488722)]
theorem point_links_checked32887 : (cuts32887.take 1).map (fun c => (4314497025-1+2*2^10*c.k,106394910151571+c.lower,106395294136229+c.upper)) = pointBounds32887 := by
 decide +kernel
def cuts32888 : List PrefixCut := [⟨26,154676806,154676902⟩,
⟨64,381763126,381763368⟩]
theorem checked32888 : checkPrefixCuts (2^48) 4314628097 10 Manual.Count131072.C032888.packed 64 cuts32888 = true := by
 decide +kernel
def pointBounds32888 : List (Nat × Nat × Nat) := [(4314681344,106395447712241,106395831697244)]
theorem point_links_checked32888 : (cuts32888.take 1).map (fun c => (4314628097-1+2*2^10*c.k,106395293035435+c.lower,106395677020342+c.upper)) = pointBounds32888 := by
 decide +kernel
def cuts32889 : List PrefixCut := [⟨28,167719009,167719118⟩,
⟨64,386578891,386579140⟩]
theorem checked32889 : checkPrefixCuts (2^48) 4314759169 10 Manual.Count131072.C032889.packed 64 cuts32889 = true := by
 decide +kernel
def pointBounds32889 : List (Nat × Nat × Nat) := [(4314816512,106395842517570,106396226502828)]
theorem point_links_checked32889 : (cuts32889.take 1).map (fun c => (4314759169-1+2*2^10*c.k,106395674798561+c.lower,106396058783710+c.upper)) = pointBounds32889 := by
 decide +kernel
def cuts32890 : List PrefixCut := [⟨30,183434973,183435088⟩,
⟨64,391068218,391068466⟩]
theorem checked32890 : checkPrefixCuts (2^48) 4314890241 10 Manual.Count131072.C032890.packed 64 cuts32890 = true := by
 decide +kernel
def pointBounds32890 : List (Nat × Nat × Nat) := [(4314951680,106396244812425,106396628797938)]
theorem point_links_checked32890 : (cuts32890.take 1).map (fun c => (4314890241-1+2*2^10*c.k,106396061377452+c.lower,106396445362850+c.upper)) = pointBounds32890 := by
 decide +kernel
def cuts32891 : List PrefixCut := [⟨32,193018275,193018400⟩,
⟨64,385250832,385251080⟩]
theorem checked32891 : checkPrefixCuts (2^48) 4315021313 10 Manual.Count131072.C032891.packed 64 cuts32891 = true := by
 decide +kernel
def pointBounds32891 : List (Nat × Nat × Nat) := [(4315086848,106396645463945,106397029449716)]
theorem point_links_checked32891 : (cuts32891.take 1).map (fun c => (4315021313-1+2*2^10*c.k,106396452445670+c.lower,106396836431316+c.upper)) = pointBounds32891 := by
 decide +kernel
def cuts32892 : List PrefixCut := [⟨34,203057534,203057663⟩,
⟨64,387652517,387652763⟩]
theorem checked32892 : checkPrefixCuts (2^48) 4315152385 10 Manual.Count131072.C032892.packed 64 cuts32892 = true := by
 decide +kernel
def pointBounds32892 : List (Nat × Nat × Nat) := [(4315222016,106397040754036,106397424740059)]
theorem point_links_checked32892 : (cuts32892.take 1).map (fun c => (4315152385-1+2*2^10*c.k,106396837696502+c.lower,106397221682396+c.upper)) = pointBounds32892 := by
 decide +kernel
def cuts32893 : List PrefixCut := [⟨36,219814585,219814722⟩,
⟨64,385553576,385553818⟩]
theorem checked32893 : checkPrefixCuts (2^48) 4315283457 10 Manual.Count131072.C032893.packed 64 cuts32893 = true := by
 decide +kernel
def pointBounds32893 : List (Nat × Nat × Nat) := [(4315357184,106397445163604,106397829149881)]
theorem point_links_checked32893 : (cuts32893.take 1).map (fun c => (4315283457-1+2*2^10*c.k,106397225349019+c.lower,106397609335159+c.upper)) = pointBounds32893 := by
 decide +kernel
def cuts32894 : List PrefixCut := [⟨38,225156251,225156394⟩,
⟨64,383193712,383193956⟩]
theorem checked32894 : checkPrefixCuts (2^48) 4315414529 10 Manual.Count131072.C032894.packed 64 cuts32894 = true := by
 decide +kernel
def pointBounds32894 : List (Nat × Nat × Nat) := [(4315492352,106397836058846,106398220045371)]
theorem point_links_checked32894 : (cuts32894.take 1).map (fun c => (4315414529-1+2*2^10*c.k,106397610902595+c.lower,106397994888977+c.upper)) = pointBounds32894 := by
 decide +kernel
def cuts32895 : List PrefixCut := [⟨40,241846332,241846486⟩,
⟨64,387943312,387943561⟩]
theorem checked32895 : checkPrefixCuts (2^48) 4315545601 10 Manual.Count131072.C032895.packed 64 cuts32895 = true := by
 decide +kernel
def pointBounds32895 : List (Nat × Nat × Nat) := [(4315627520,106398235942639,106398619929419)]
theorem point_links_checked32895 : (cuts32895.take 1).map (fun c => (4315545601-1+2*2^10*c.k,106397994096307+c.lower,106398378082933+c.upper)) = pointBounds32895 := by
 decide +kernel
def cuts32896 : List PrefixCut := [⟨42,249600158,249600321⟩,
⟨64,382974767,382975014⟩]
theorem checked32896 : checkPrefixCuts (2^48) 4315676673 10 Manual.Count131072.C032896.packed 64 cuts32896 = true := by
 decide +kernel
def pointBounds32896 : List (Nat × Nat × Nat) := [(4315762688,106398631639777,106399015626815)]
theorem point_links_checked32896 : (cuts32896.take 1).map (fun c => (4315676673-1+2*2^10*c.k,106398382039619+c.lower,106398766026494+c.upper)) = pointBounds32896 := by
 decide +kernel
def cuts32897 : List PrefixCut := [⟨44,265831940,265832110⟩,
⟨64,387919744,387919989⟩]
theorem checked32897 : checkPrefixCuts (2^48) 4315807745 10 Manual.Count131072.C032897.packed 64 cuts32897 = true := by
 decide +kernel
def pointBounds32897 : List (Nat × Nat × Nat) := [(4315897856,106399030846326,106399414833618)]
theorem point_links_checked32897 : (cuts32897.take 1).map (fun c => (4315807745-1+2*2^10*c.k,106398765014386+c.lower,106399149001508+c.upper)) = pointBounds32897 := by
 decide +kernel
def cuts32898 : List PrefixCut := [⟨46,278606266,278606444⟩,
⟨64,388625369,388625616⟩]
theorem checked32898 : checkPrefixCuts (2^48) 4315938817 10 Manual.Count131072.C032898.packed 64 cuts32898 = true := by
 decide +kernel
def pointBounds32898 : List (Nat × Nat × Nat) := [(4316033024,106399431540396,106399815527941)]
theorem point_links_checked32898 : (cuts32898.take 1).map (fun c => (4315938817-1+2*2^10*c.k,106399152934130+c.lower,106399536921497+c.upper)) = pointBounds32898 := by
 decide +kernel
def cuts32899 : List PrefixCut := [⟨48,291053706,291053891⟩,
⟨64,387504948,387505195⟩]
theorem checked32899 : checkPrefixCuts (2^48) 4316069889 10 Manual.Count131072.C032899.packed 64 cuts32899 = true := by
 decide +kernel
def pointBounds32899 : List (Nat × Nat × Nat) := [(4316168192,106399832613205,106400216601004)]
theorem point_links_checked32899 : (cuts32899.take 1).map (fun c => (4316069889-1+2*2^10*c.k,106399541559499+c.lower,106399925547113+c.upper)) = pointBounds32899 := by
 decide +kernel
def cuts32900 : List PrefixCut := [⟨50,293848885,293849076⟩,
⟨64,377515633,377515877⟩]
theorem checked32900 : checkPrefixCuts (2^48) 4316200961 10 Manual.Count131072.C032900.packed 64 cuts32900 = true := by
 decide +kernel
def pointBounds32900 : List (Nat × Nat × Nat) := [(4316303360,106400222913332,106400606901384)]
theorem point_links_checked32900 : (cuts32900.take 1).map (fun c => (4316200961-1+2*2^10*c.k,106399929064447+c.lower,106400313052308+c.upper)) = pointBounds32900 := by
 decide +kernel
def cuts32901 : List PrefixCut := [⟨52,312620529,312620724⟩,
⟨64,383438370,383438610⟩]
theorem checked32901 : checkPrefixCuts (2^48) 4316332033 10 Manual.Count131072.C032901.packed 64 cuts32901 = true := by
 decide +kernel
def pointBounds32901 : List (Nat × Nat × Nat) := [(4316438528,106400619200609,106401003188909)]
theorem point_links_checked32901 : (cuts32901.take 1).map (fun c => (4316332033-1+2*2^10*c.k,106400306580080+c.lower,106400690568185+c.upper)) = pointBounds32901 := by
 decide +kernel
def cuts32902 : List PrefixCut := [⟨54,324413663,324413874⟩,
⟨64,383687544,383687792⟩]
theorem checked32902 : checkPrefixCuts (2^48) 4316463105 10 Manual.Count131072.C032902.packed 64 cuts32902 = true := by
 decide +kernel
def pointBounds32902 : List (Nat × Nat × Nat) := [(4316573696,106401014432113,106401398420669)]
theorem point_links_checked32902 : (cuts32902.take 1).map (fun c => (4316463105-1+2*2^10*c.k,106400690018450+c.lower,106401074006795+c.upper)) = pointBounds32902 := by
 decide +kernel
def cuts32903 : List PrefixCut := [⟨56,345465437,345465658⟩,
⟨64,393196065,393196316⟩]
theorem checked32903 : checkPrefixCuts (2^48) 4316594177 10 Manual.Count131072.C032903.packed 64 cuts32903 = true := by
 decide +kernel
def pointBounds32903 : List (Nat × Nat × Nat) := [(4316708864,106401419171431,106401803160245)]
theorem point_links_checked32903 : (cuts32903.take 1).map (fun c => (4316594177-1+2*2^10*c.k,106401073705994+c.lower,106401457694587+c.upper)) = pointBounds32903 := by
 decide +kernel
def cuts32904 : List PrefixCut := [⟨58,348062946,348063164⟩,
⟨64,381903701,381903940⟩]
theorem checked32904 : checkPrefixCuts (2^48) 4316725249 10 Manual.Count131072.C032904.packed 64 cuts32904 = true := by
 decide +kernel
def pointBounds32904 : List (Nat × Nat × Nat) := [(4316844032,106401814965005,106402198954067)]
theorem point_links_checked32904 : (cuts32904.take 1).map (fun c => (4316725249-1+2*2^10*c.k,106401466902059+c.lower,106401850890903+c.upper)) = pointBounds32904 := by
 decide +kernel
def cuts32905 : List PrefixCut := [⟨60,363440077,363440304⟩,
⟨64,388086341,388086583⟩]
theorem checked32905 : checkPrefixCuts (2^48) 4316856321 10 Manual.Count131072.C032905.packed 64 cuts32905 = true := by
 decide +kernel
def pointBounds32905 : List (Nat × Nat × Nat) := [(4316979200,106402212245837,106402596235147)]
theorem point_links_checked32905 : (cuts32905.take 1).map (fun c => (4316856321-1+2*2^10*c.k,106401848805760+c.lower,106402232794843+c.upper)) = pointBounds32905 := by
 decide +kernel
def cuts32906 : List PrefixCut := [⟨62,376208208,376208453⟩,
⟨64,388074562,388074814⟩]
theorem checked32906 : checkPrefixCuts (2^48) 4316987393 10 Manual.Count131072.C032906.packed 64 cuts32906 = true := by
 decide +kernel
def pointBounds32906 : List (Nat × Nat × Nat) := [(4317114368,106402613100309,106402997089879)]
theorem point_links_checked32906 : (cuts32906.take 1).map (fun c => (4316987393-1+2*2^10*c.k,106402236892101+c.lower,106402620881426+c.upper)) = pointBounds32906 := by
 decide +kernel
def cuts32907 : List PrefixCut := [⟨64,385585217,385585461⟩]
theorem checked32907 : checkPrefixCuts (2^48) 4317118465 10 Manual.Count131072.C032907.packed 64 cuts32907 = true := by
 decide +kernel
def pointBounds32907 : List (Nat × Nat × Nat) := [(4317249536,106403010551880,106403394541701)]
theorem point_links_checked32907 : (cuts32907.take 1).map (fun c => (4317118465-1+2*2^10*c.k,106402624966663+c.lower,106403008956240+c.upper)) = pointBounds32907 := by
 decide +kernel
def cuts32908 : List PrefixCut := [⟨64,386551558,386551804⟩]
theorem checked32908 : checkPrefixCuts (2^48) 4317249537 10 Manual.Count131072.C032908.packed 64 cuts32908 = true := by
 decide +kernel
def cuts32909 : List PrefixCut := [⟨2,12061209,12061217⟩,
⟨64,382823646,382823889⟩]
theorem checked32909 : checkPrefixCuts (2^48) 4317380609 10 Manual.Count131072.C032909.packed 64 cuts32909 = true := by
 decide +kernel
def pointBounds32909 : List (Nat × Nat × Nat) := [(4317384704,106403409164647,106403793154722)]
theorem point_links_checked32909 : (cuts32909.take 1).map (fun c => (4317380609-1+2*2^10*c.k,106403397103438+c.lower,106403781093505+c.upper)) = pointBounds32909 := by
 decide +kernel
def cuts32910 : List PrefixCut := [⟨4,23404543,23404558⟩,
⟨64,388744528,388744777⟩]
theorem checked32910 : checkPrefixCuts (2^48) 4317511681 10 Manual.Count131072.C032910.packed 64 cuts32910 = true := by
 decide +kernel
def pointBounds32910 : List (Nat × Nat × Nat) := [(4317519872,106403803331627,106404187321952)]
theorem point_links_checked32910 : (cuts32910.take 1).map (fun c => (4317511681-1+2*2^10*c.k,106403779927084+c.lower,106404163917394+c.upper)) = pointBounds32910 := by
 decide +kernel
def cuts32911 : List PrefixCut := [⟨6,36311779,36311802⟩,
⟨64,382278879,382279127⟩]
theorem checked32911 : checkPrefixCuts (2^48) 4317642753 10 Manual.Count131072.C032911.packed 64 cuts32911 = true := by
 decide +kernel
def pointBounds32911 : List (Nat × Nat × Nat) := [(4317655040,106404204983391,106404588973973)]
theorem point_links_checked32911 : (cuts32911.take 1).map (fun c => (4317642753-1+2*2^10*c.k,106404168671612+c.lower,106404552662171+c.upper)) = pointBounds32911 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000090
