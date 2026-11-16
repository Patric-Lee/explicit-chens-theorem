import PlattAssemblyKernel
import PlattCertificates.Count131072.C016880
import PlattCertificates.Count131072.C016881
import PlattCertificates.Count131072.C016882
import PlattCertificates.Count131072.C016883
import PlattCertificates.Count131072.C016884
import PlattCertificates.Count131072.C016885
import PlattCertificates.Count131072.C016886
import PlattCertificates.Count131072.C016887
import PlattCertificates.Count131072.C016888
import PlattCertificates.Count131072.C016889
import PlattCertificates.Count131072.C016890
import PlattCertificates.Count131072.C016891
import PlattCertificates.Count131072.C016892
import PlattCertificates.Count131072.C016893
import PlattCertificates.Count131072.C016894
import PlattCertificates.Count131072.C016895
import PlattCertificates.Count131072.C016896
import PlattCertificates.Count131072.C016897
import PlattCertificates.Count131072.C016898
import PlattCertificates.Count131072.C016899
import PlattCertificates.Count131072.C016900
import PlattCertificates.Count131072.C016901
import PlattCertificates.Count131072.C016902
import PlattCertificates.Count131072.C016903
import PlattCertificates.Count131072.C016904
import PlattCertificates.Count131072.C016905
import PlattCertificates.Count131072.C016906
import PlattCertificates.Count131072.C016907
import PlattCertificates.Count131072.C016908
import PlattCertificates.Count131072.C016909
import PlattCertificates.Count131072.C016910
import PlattCertificates.Count131072.C016911
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000215
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts16880 : List PrefixCut := [⟨40,244081806,244081960⟩,
⟨108,659594713,659595125⟩,
⟨128,783915903,783916391⟩]
theorem checked16880 : checkPrefixCuts (2^48) 2216427521 9 Manual.Count131072.C016880.packed 128 cuts16880 = true := by
 decide +kernel
def pointBounds16880 : List (Nat × Nat × Nat) := [(2216468480,97814813004972,97815192037383),(2216538112,97815228517879,97815607550548)]
theorem point_links_checked16880 : (cuts16880.take 2).map (fun c => (2216427521-1+2*2^9*c.k,97814568923166+c.lower,97814947955423+c.upper)) = pointBounds16880 := by
 decide +kernel
def cuts16881 : List PrefixCut := [⟨48,283940564,283940741⟩,
⟨116,694602110,694602541⟩,
⟨128,768250617,768251095⟩]
theorem checked16881 : checkPrefixCuts (2^48) 2216558593 9 Manual.Count131072.C016881.packed 128 cuts16881 = true := by
 decide +kernel
def pointBounds16881 : List (Nat × Nat × Nat) := [(2216607744,97815636779633,97816015812555),(2216677376,97816047441179,97816426474355)]
theorem point_links_checked16881 : (cuts16881.take 2).map (fun c => (2216558593-1+2*2^9*c.k,97815352839069+c.lower,97815731871814+c.upper)) = pointBounds16881 := by
 decide +kernel
def cuts16882 : List PrefixCut := [⟨56,337127148,337127357⟩,
⟨124,749921384,749921852⟩,
⟨128,772903398,772903880⟩]
theorem checked16882 : checkPrefixCuts (2^48) 2216689665 9 Manual.Count131072.C016882.packed 128 cuts16882 = true := by
 decide +kernel
def pointBounds16882 : List (Nat × Nat × Nat) := [(2216747008,97816458216834,97816837250266),(2216816640,97816871011070,97817250044761)]
theorem point_links_checked16882 : (cuts16882.take 2).map (fun c => (2216689665-1+2*2^9*c.k,97816121089686+c.lower,97816500122909+c.upper)) = pointBounds16882 := by
 decide +kernel
def cuts16883 : List PrefixCut := [⟨64,384339510,384339753⟩,
⟨128,764985684,764986162⟩]
theorem checked16883 : checkPrefixCuts (2^48) 2216820737 9 Manual.Count131072.C016883.packed 128 cuts16883 = true := by
 decide +kernel
def pointBounds16883 : List (Nat × Nat × Nat) := [(2216886272,97817278332594,97817657366542)]
theorem point_links_checked16883 : (cuts16883.take 1).map (fun c => (2216820737-1+2*2^9*c.k,97816893993084+c.lower,97817273026789+c.upper)) = pointBounds16883 := by
 decide +kernel
def cuts16884 : List PrefixCut := [⟨4,25012048,25012063⟩,
⟨72,439544906,439545179⟩,
⟨128,781572345,781572835⟩]
theorem checked16884 : checkPrefixCuts (2^48) 2216951809 9 Manual.Count131072.C016884.packed 128 cuts16884 = true := by
 decide +kernel
def pointBounds16884 : List (Nat × Nat × Nat) := [(2216955904,97817683990816,97818063025014),(2217025536,97818098523674,97818477558130)]
theorem point_links_checked16884 : (cuts16884.take 2).map (fun c => (2216951809-1+2*2^9*c.k,97817658978768+c.lower,97818038012951+c.upper)) = pointBounds16884 := by
 decide +kernel
def cuts16885 : List PrefixCut := [⟨12,74269819,74269866⟩,
⟨80,486237569,486237880⟩,
⟨128,772766469,772766961⟩]
theorem checked16885 : checkPrefixCuts (2^48) 2217082881 9 Manual.Count131072.C016885.packed 128 cuts16885 = true := by
 decide +kernel
def pointBounds16885 : List (Nat × Nat × Nat) := [(2217095168,97818514820932,97818893855652),(2217164800,97818926788682,97819305823666)]
theorem point_links_checked16885 : (cuts16885.take 2).map (fun c => (2217082881-1+2*2^9*c.k,97818440551113+c.lower,97818819585786+c.upper)) = pointBounds16885 := by
 decide +kernel
def cuts16886 : List PrefixCut := [⟨20,121363449,121363525⟩,
⟨88,530893337,530893671⟩,
⟨128,774878688,774879176⟩]
theorem checked16886 : checkPrefixCuts (2^48) 2217213953 9 Manual.Count131072.C016886.packed 128 cuts16886 = true := by
 decide +kernel
def pointBounds16886 : List (Nat × Nat × Nat) := [(2217234432,97819334681031,97819713716272),(2217304064,97819744210919,97820123246418)]
theorem point_links_checked16886 : (cuts16886.take 2).map (fun c => (2217213953-1+2*2^9*c.k,97819213317582+c.lower,97819592352747+c.upper)) = pointBounds16886 := by
 decide +kernel
def cuts16887 : List PrefixCut := [⟨28,167435814,167435922⟩,
⟨96,583540697,583541070⟩,
⟨128,778006264,778006756⟩]
theorem checked16887 : checkPrefixCuts (2^48) 2217345025 9 Manual.Count131072.C016887.packed 128 cuts16887 = true := by
 decide +kernel
def pointBounds16887 : List (Nat × Nat × Nat) := [(2217373696,97820155632084,97820534667845),(2217443328,97820571736967,97820950772993)]
theorem point_links_checked16887 : (cuts16887.take 2).map (fun c => (2217345025-1+2*2^9*c.k,97819988196270+c.lower,97820367231923+c.upper)) = pointBounds16887 := by
 decide +kernel
def cuts16888 : List PrefixCut := [⟨36,220737781,220737918⟩,
⟨104,628439161,628439553⟩,
⟨128,773264013,773264497⟩]
theorem checked16888 : checkPrefixCuts (2^48) 2217476097 9 Manual.Count131072.C016888.packed 128 cuts16888 = true := by
 decide +kernel
def pointBounds16888 : List (Nat × Nat × Nat) := [(2217512960,97820986940315,97821365976597),(2217582592,97821394641695,97821773678232)]
theorem point_links_checked16888 : (cuts16888.take 2).map (fun c => (2217476097-1+2*2^9*c.k,97820766202534+c.lower,97821145238679+c.upper)) = pointBounds16888 := by
 decide +kernel
def cuts16889 : List PrefixCut := [⟨44,258548275,258548445⟩,
⟨112,662543275,662543700⟩,
⟨128,760018039,760018526⟩]
theorem checked16889 : checkPrefixCuts (2^48) 2217607169 9 Manual.Count131072.C016889.packed 128 cuts16889 = true := by
 decide +kernel
def pointBounds16889 : List (Nat × Nat × Nat) := [(2217652224,97821798014822,97822177051621),(2217721856,97822202009822,97822581046876)]
theorem point_links_checked16889 : (cuts16889.take 2).map (fun c => (2217607169-1+2*2^9*c.k,97821539466547+c.lower,97821918503176+c.upper)) = pointBounds16889 := by
 decide +kernel
def cuts16890 : List PrefixCut := [⟨52,307776817,307777007⟩,
⟨120,726214747,726215192⟩,
⟨128,776218286,776218763⟩]
theorem checked16890 : checkPrefixCuts (2^48) 2217738241 9 Manual.Count131072.C016890.packed 128 cuts16890 = true := by
 decide +kernel
def pointBounds16890 : List (Nat × Nat × Nat) := [(2217791488,97822607261403,97822986298709),(2217861120,97823025699333,97823404736894)]
theorem point_links_checked16890 : (cuts16890.take 2).map (fun c => (2217738241-1+2*2^9*c.k,97822299484586+c.lower,97822678521702+c.upper)) = pointBounds16890 := by
 decide +kernel
def cuts16891 : List PrefixCut := [⟨60,355476477,355476701⟩,
⟨128,762085816,762086291⟩]
theorem checked16891 : checkPrefixCuts (2^48) 2217869313 9 Manual.Count131072.C016891.packed 128 cuts16891 = true := by
 decide +kernel
def pointBounds16891 : List (Nat × Nat × Nat) := [(2217930752,97823431179349,97823810217166),(2218000384,97823837788688,97824216826756)]
theorem point_links_checked16891 : (cuts16891.take 2).map (fun c => (2217869313-1+2*2^9*c.k,97823075702872+c.lower,97823454740465+c.upper)) = pointBounds16891 := by
 decide +kernel
def cuts16892 : List PrefixCut := [⟨68,411799589,411799847⟩,
⟨128,777141957,777142443⟩]
theorem checked16892 : checkPrefixCuts (2^48) 2218000385 9 Manual.Count131072.C016892.packed 128 cuts16892 = true := by
 decide +kernel
def pointBounds16892 : List (Nat × Nat × Nat) := [(2218070016,97824249588277,97824628626603)]
theorem point_links_checked16892 : (cuts16892.take 1).map (fun c => (2218000385-1+2*2^9*c.k,97823837788688+c.lower,97824216826756+c.upper)) = pointBounds16892 := by
 decide +kernel
def cuts16893 : List PrefixCut := [⟨8,47586400,47586432⟩,
⟨76,458091160,458091445⟩,
⟨128,771639652,771640132⟩]
theorem checked16893 : checkPrefixCuts (2^48) 2218131457 9 Manual.Count131072.C016893.packed 128 cuts16893 = true := by
 decide +kernel
def pointBounds16893 : List (Nat × Nat × Nat) := [(2218139648,97824662517045,97825041555631),(2218209280,97825073021805,97825452060644)]
theorem point_links_checked16893 : (cuts16893.take 2).map (fun c => (2218131457-1+2*2^9*c.k,97824614930645+c.lower,97824993969199+c.upper)) = pointBounds16893 := by
 decide +kernel
def cuts16894 : List PrefixCut := [⟨16,99608137,99608198⟩,
⟨84,516177745,516178069⟩,
⟨128,778953635,778954127⟩]
theorem checked16894 : checkPrefixCuts (2^48) 2218262529 9 Manual.Count131072.C016894.packed 128 cuts16894 = true := by
 decide +kernel
def pointBounds16894 : List (Nat × Nat × Nat) := [(2218278912,97825486178434,97825865217529),(2218348544,97825902748042,97826281787400)]
theorem point_links_checked16894 : (cuts16894.take 2).map (fun c => (2218262529-1+2*2^9*c.k,97825386570297+c.lower,97825765609331+c.upper)) = pointBounds16894 := by
 decide +kernel
def cuts16895 : List PrefixCut := [⟨24,148959000,148959092⟩,
⟨92,554717704,554718051⟩,
⟨128,767488546,767489027⟩]
theorem checked16895 : checkPrefixCuts (2^48) 2218393601 9 Manual.Count131072.C016895.packed 128 cuts16895 = true := by
 decide +kernel
def pointBounds16895 : List (Nat × Nat × Nat) := [(2218418176,97826314482932,97826693522550),(2218487808,97826720241636,97827099281509)]
theorem point_links_checked16895 : (cuts16895.take 2).map (fun c => (2218393601-1+2*2^9*c.k,97826165523932+c.lower,97826544563458+c.upper)) = pointBounds16895 := by
 decide +kernel
def cuts16896 : List PrefixCut := [⟨32,195766379,195766502⟩,
⟨100,603783394,603783772⟩,
⟨128,768331358,768331839⟩]
theorem checked16896 : checkPrefixCuts (2^48) 2218524673 9 Manual.Count131072.C016896.packed 128 cuts16896 = true := by
 decide +kernel
def pointBounds16896 : List (Nat × Nat × Nat) := [(2218557440,97827128778857,97827507818987),(2218627072,97827536795872,97827915836257)]
theorem point_links_checked16896 : (cuts16896.take 2).map (fun c => (2218524673-1+2*2^9*c.k,97826933012478+c.lower,97827312052485+c.upper)) = pointBounds16896 := by
 decide +kernel
def cuts16897 : List PrefixCut := [⟨40,241299407,241299552⟩,
⟨108,652589161,652589568⟩,
⟨128,772725957,772726439⟩]
theorem checked16897 : checkPrefixCuts (2^48) 2218655745 9 Manual.Count131072.C016897.packed 128 cuts16897 = true := by
 decide +kernel
def pointBounds16897 : List (Nat × Nat × Nat) := [(2218696704,97827942643243,97828321683876),(2218766336,97828353932997,97828732973892)]
theorem point_links_checked16897 : (cuts16897.take 2).map (fun c => (2218655745-1+2*2^9*c.k,97827701343836+c.lower,97828080384324+c.upper)) = pointBounds16897 := by
 decide +kernel
def cuts16898 : List PrefixCut := [⟨48,291647432,291647617⟩,
⟨116,702911378,702911821⟩,
⟨128,778135012,778135504⟩]
theorem checked16898 : checkPrefixCuts (2^48) 2218786817 9 Manual.Count131072.C016898.packed 128 cuts16898 = true := by
 decide +kernel
def pointBounds16898 : List (Nat × Nat × Nat) := [(2218835968,97828765717225,97829144758380),(2218905600,97829176981171,97829556022584)]
theorem point_links_checked16898 : (cuts16898.take 2).map (fun c => (2218786817-1+2*2^9*c.k,97828474069793+c.lower,97828853110763+c.upper)) = pointBounds16898 := by
 decide +kernel
def cuts16899 : List PrefixCut := [⟨56,338183966,338184179⟩,
⟨124,747519341,747519813⟩,
⟨128,771112502,771112988⟩]
theorem checked16899 : checkPrefixCuts (2^48) 2218917889 9 Manual.Count131072.C016899.packed 128 cuts16899 = true := by
 decide +kernel
def pointBounds16899 : List (Nat × Nat × Nat) := [(2218975232,97829590388771,97829969430446),(2219044864,97829999724146,97830378766080)]
theorem point_links_checked16899 : (cuts16899.take 2).map (fun c => (2218917889-1+2*2^9*c.k,97829252204805+c.lower,97829631246267+c.upper)) = pointBounds16899 := by
 decide +kernel
def cuts16900 : List PrefixCut := [⟨64,386490501,386490744⟩,
⟨128,775379483,775379973⟩]
theorem checked16900 : checkPrefixCuts (2^48) 2219048961 9 Manual.Count131072.C016900.packed 128 cuts16900 = true := by
 decide +kernel
def pointBounds16900 : List (Nat × Nat × Nat) := [(2219114496,97830409807808,97830788849999)]
theorem point_links_checked16900 : (cuts16900.take 1).map (fun c => (2219048961-1+2*2^9*c.k,97830023317307+c.lower,97830402359255+c.upper)) = pointBounds16900 := by
 decide +kernel
def cuts16901 : List PrefixCut := [⟨4,24225910,24225925⟩,
⟨72,440625573,440625851⟩,
⟨128,780533985,780534475⟩]
theorem checked16901 : checkPrefixCuts (2^48) 2219180033 9 Manual.Count131072.C016901.packed 128 cuts16901 = true := by
 decide +kernel
def pointBounds16901 : List (Nat × Nat × Nat) := [(2219184128,97830822922700,97831201965153),(2219253760,97831239322363,97831618365079)]
theorem point_links_checked16901 : (cuts16901.take 2).map (fun c => (2219180033-1+2*2^9*c.k,97830798696790+c.lower,97831177739228+c.upper)) = pointBounds16901 := by
 decide +kernel
def cuts16902 : List PrefixCut := [⟨12,74068426,74068472⟩,
⟨80,484354261,484354567⟩,
⟨128,776175734,776176218⟩]
theorem checked16902 : checkPrefixCuts (2^48) 2219311105 9 Manual.Count131072.C016902.packed 128 cuts16902 = true := by
 decide +kernel
def pointBounds16902 : List (Nat × Nat × Nat) := [(2219323392,97831653299201,97832032342175),(2219393024,97832063585036,97832442628270)]
theorem point_links_checked16902 : (cuts16902.take 2).map (fun c => (2219311105-1+2*2^9*c.k,97831579230775+c.lower,97831958273703+c.upper)) = pointBounds16902 := by
 decide +kernel
def cuts16903 : List PrefixCut := [⟨20,119212447,119212521⟩,
⟨88,533530714,533531051⟩,
⟨128,774481193,774481679⟩]
theorem checked16903 : checkPrefixCuts (2^48) 2219442177 9 Manual.Count131072.C016903.packed 128 cuts16903 = true := by
 decide +kernel
def pointBounds16903 : List (Nat × Nat × Nat) := [(2219462656,97832474618956,97832853662442),(2219532288,97832888937223,97833267980972)]
theorem point_links_checked16903 : (cuts16903.take 2).map (fun c => (2219442177-1+2*2^9*c.k,97832355406509+c.lower,97832734449921+c.upper)) = pointBounds16903 := by
 decide +kernel
def cuts16904 : List PrefixCut := [⟨28,168789477,168789583⟩,
⟨96,571922345,571922705⟩,
⟨128,766826707,766827187⟩]
theorem checked16904 : checkPrefixCuts (2^48) 2219573249 9 Manual.Count131072.C016904.packed 128 cuts16904 = true := by
 decide +kernel
def pointBounds16904 : List (Nat × Nat × Nat) := [(2219601920,97833298677179,97833677721183),(2219671552,97833701810047,97834080854305)]
theorem point_links_checked16904 : (cuts16904.take 2).map (fun c => (2219573249-1+2*2^9*c.k,97833129887702+c.lower,97833508931600+c.upper)) = pointBounds16904 := by
 decide +kernel
def cuts16905 : List PrefixCut := [⟨36,214302659,214302797⟩,
⟨104,626920467,626920861⟩,
⟨128,775911173,775911658⟩]
theorem checked16905 : checkPrefixCuts (2^48) 2219704321 9 Manual.Count131072.C016905.packed 128 cuts16905 = true := by
 decide +kernel
def pointBounds16905 : List (Nat × Nat × Nat) := [(2219741184,97834111017068,97834490061584),(2219810816,97834523634876,97834902679648)]
theorem point_links_checked16905 : (cuts16905.take 2).map (fun c => (2219704321-1+2*2^9*c.k,97833896714409+c.lower,97834275758787+c.upper)) = pointBounds16905 := by
 decide +kernel
def cuts16906 : List PrefixCut := [⟨44,265769857,265770022⟩,
⟨112,674177652,674178074⟩,
⟨128,771808170,771808652⟩]
theorem checked16906 : checkPrefixCuts (2^48) 2219835393 9 Manual.Count131072.C016906.packed 128 cuts16906 = true := by
 decide +kernel
def pointBounds16906 : List (Nat × Nat × Nat) := [(2219880448,97834938395439,97835317440467),(2219950080,97835346803234,97835725848519)]
theorem point_links_checked16906 : (cuts16906.take 2).map (fun c => (2219835393-1+2*2^9*c.k,97834672625582+c.lower,97835051670445+c.upper)) = pointBounds16906 := by
 decide +kernel
def cuts16907 : List PrefixCut := [⟨52,317991547,317991745⟩,
⟨120,728909507,728909966⟩,
⟨128,778862854,778863346⟩]
theorem checked16907 : checkPrefixCuts (2^48) 2219966465 9 Manual.Count131072.C016907.packed 128 cuts16907 = true := by
 decide +kernel
def pointBounds16907 : List (Nat × Nat × Nat) := [(2220019712,97835762425299,97836141470842),(2220089344,97836173343259,97836552389063)]
theorem point_links_checked16907 : (cuts16907.take 2).map (fun c => (2219966465-1+2*2^9*c.k,97835444433752+c.lower,97835823479097+c.upper)) = pointBounds16907 := by
 decide +kernel
def cuts16908 : List PrefixCut := [⟨60,366403376,366403608⟩,
⟨128,769942337,769942825⟩]
theorem checked16908 : checkPrefixCuts (2^48) 2220097537 9 Manual.Count131072.C016908.packed 128 cuts16908 = true := by
 decide +kernel
def pointBounds16908 : List (Nat × Nat × Nat) := [(2220158976,97836589699982,97836968746051),(2220228608,97836993238943,97837372285268)]
theorem point_links_checked16908 : (cuts16908.take 2).map (fun c => (2220097537-1+2*2^9*c.k,97836223296606+c.lower,97836602342443+c.upper)) = pointBounds16908 := by
 decide +kernel
def cuts16909 : List PrefixCut := [⟨68,416964475,416964738⟩,
⟨128,771164587,771165076⟩]
theorem checked16909 : checkPrefixCuts (2^48) 2220228609 9 Manual.Count131072.C016909.packed 128 cuts16909 = true := by
 decide +kernel
def pointBounds16909 : List (Nat × Nat × Nat) := [(2220298240,97837410203418,97837789250006)]
theorem point_links_checked16909 : (cuts16909.take 1).map (fun c => (2220228609-1+2*2^9*c.k,97836993238943+c.lower,97837372285268+c.upper)) = pointBounds16909 := by
 decide +kernel
def cuts16910 : List PrefixCut := [⟨8,48806337,48806369⟩,
⟨76,464730490,464730780⟩,
⟨128,783415178,783415665⟩]
theorem checked16910 : checkPrefixCuts (2^48) 2220359681 9 Manual.Count131072.C016910.packed 128 cuts16910 = true := by
 decide +kernel
def pointBounds16910 : List (Nat × Nat × Nat) := [(2220367872,97837813209867,97838192256713),(2220437504,97838229134020,97838608181124)]
theorem point_links_checked16910 : (cuts16910.take 2).map (fun c => (2220359681-1+2*2^9*c.k,97837764403530+c.lower,97838143450344+c.upper)) = pointBounds16910 := by
 decide +kernel
def cuts16911 : List PrefixCut := [⟨16,96592648,96592711⟩,
⟨84,509321769,509322090⟩,
⟨128,778678826,778679314⟩]
theorem checked16911 : checkPrefixCuts (2^48) 2220490753 9 Manual.Count131072.C016911.packed 128 cuts16911 = true := by
 decide +kernel
def pointBounds16911 : List (Nat × Nat × Nat) := [(2220507136,97838644411356,97839023458720),(2220576768,97839057140477,97839436188099)]
theorem point_links_checked16911 : (cuts16911.take 2).map (fun c => (2220490753-1+2*2^9*c.k,97838547818708+c.lower,97838926866009+c.upper)) = pointBounds16911 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000215
