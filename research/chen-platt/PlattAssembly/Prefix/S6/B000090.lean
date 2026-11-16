import PlattAssemblyKernel
import PlattCertificates.Count131072.C052880
import PlattCertificates.Count131072.C052881
import PlattCertificates.Count131072.C052882
import PlattCertificates.Count131072.C052883
import PlattCertificates.Count131072.C052884
import PlattCertificates.Count131072.C052885
import PlattCertificates.Count131072.C052886
import PlattCertificates.Count131072.C052887
import PlattCertificates.Count131072.C052888
import PlattCertificates.Count131072.C052889
import PlattCertificates.Count131072.C052890
import PlattCertificates.Count131072.C052891
import PlattCertificates.Count131072.C052892
import PlattCertificates.Count131072.C052893
import PlattCertificates.Count131072.C052894
import PlattCertificates.Count131072.C052895
import PlattCertificates.Count131072.C052896
import PlattCertificates.Count131072.C052897
import PlattCertificates.Count131072.C052898
import PlattCertificates.Count131072.C052899
import PlattCertificates.Count131072.C052900
import PlattCertificates.Count131072.C052901
import PlattCertificates.Count131072.C052902
import PlattCertificates.Count131072.C052903
import PlattCertificates.Count131072.C052904
import PlattCertificates.Count131072.C052905
import PlattCertificates.Count131072.C052906
import PlattCertificates.Count131072.C052907
import PlattCertificates.Count131072.C052908
import PlattCertificates.Count131072.C052909
import PlattCertificates.Count131072.C052910
import PlattCertificates.Count131072.C052911
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000090
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts52880 : List PrefixCut := [⟨64,237515625,237515754⟩]
theorem checked52880 : checkPrefixCuts (2^48) 6935019521 10 Manual.Count131072.C052880.packed 64 cuts52880 = true := by
 decide +kernel
def cuts52881 : List PrefixCut := [⟨28,103252148,103252207⟩,
⟨64,233330758,233330892⟩]
theorem checked52881 : checkPrefixCuts (2^48) 6935150593 10 Manual.Count131072.C052881.packed 64 cuts52881 = true := by
 decide +kernel
def pointBounds52881 : List (Nat × Nat × Nat) := [(6935207936,112353273931888,112353661449834)]
theorem point_links_checked52881 : (cuts52881.take 1).map (fun c => (6935150593-1+2*2^10*c.k,112353170679740+c.lower,112353558197627+c.upper)) = pointBounds52881 := by
 decide +kernel
def cuts52882 : List PrefixCut := [⟨64,237466094,237466227⟩]
theorem checked52882 : checkPrefixCuts (2^48) 6935281665 10 Manual.Count131072.C052882.packed 64 cuts52882 = true := by
 decide +kernel
def cuts52883 : List PrefixCut := [⟨6,21794217,21794228⟩,
⟨64,232469644,232469777⟩]
theorem checked52883 : checkPrefixCuts (2^48) 6935412737 10 Manual.Count131072.C052883.packed 64 cuts52883 = true := by
 decide +kernel
def pointBounds52883 : List (Nat × Nat × Nat) := [(6935425024,112353663270809,112354050788974)]
theorem point_links_checked52883 : (cuts52883.take 1).map (fun c => (6935412737-1+2*2^10*c.k,112353641476592+c.lower,112354028994746+c.upper)) = pointBounds52883 := by
 decide +kernel
def cuts52884 : List PrefixCut := [⟨48,173618843,173618942⟩,
⟨64,233845097,233845233⟩]
theorem checked52884 : checkPrefixCuts (2^48) 6935543809 10 Manual.Count131072.C052884.packed 64 cuts52884 = true := by
 decide +kernel
def pointBounds52884 : List (Nat × Nat × Nat) := [(6935642112,112354047565079,112354435083465)]
theorem point_links_checked52884 : (cuts52884.take 1).map (fun c => (6935543809-1+2*2^10*c.k,112353873946236+c.lower,112354261464523+c.upper)) = pointBounds52884 := by
 decide +kernel
def cuts52885 : List PrefixCut := [⟨64,236235109,236235240⟩]
theorem checked52885 : checkPrefixCuts (2^48) 6935674881 10 Manual.Count131072.C052885.packed 64 cuts52885 = true := by
 decide +kernel
def cuts52886 : List PrefixCut := [⟨26,94922962,94923016⟩,
⟨64,234363844,234363975⟩]
theorem checked52886 : checkPrefixCuts (2^48) 6935805953 10 Manual.Count131072.C052886.packed 64 cuts52886 = true := by
 decide +kernel
def pointBounds52886 : List (Nat × Nat × Nat) := [(6935859200,112354438949404,112354826468012)]
theorem point_links_checked52886 : (cuts52886.take 1).map (fun c => (6935805953-1+2*2^10*c.k,112354344026442+c.lower,112354731544996+c.upper)) = pointBounds52886 := by
 decide +kernel
def cuts52887 : List PrefixCut := [⟨64,236145022,236145155⟩]
theorem checked52887 : checkPrefixCuts (2^48) 6935937025 10 Manual.Count131072.C052887.packed 64 cuts52887 = true := by
 decide +kernel
def cuts52888 : List PrefixCut := [⟨4,15136828,15136837⟩,
⟨64,236262293,236262427⟩]
theorem checked52888 : checkPrefixCuts (2^48) 6936068097 10 Manual.Count131072.C052888.packed 64 cuts52888 = true := by
 decide +kernel
def pointBounds52888 : List (Nat × Nat × Nat) := [(6936076288,112354829672136,112355217190963)]
theorem point_links_checked52888 : (cuts52888.take 1).map (fun c => (6936068097-1+2*2^10*c.k,112354814535308+c.lower,112355202054126+c.upper)) = pointBounds52888 := by
 decide +kernel
def cuts52889 : List PrefixCut := [⟨46,168083563,168083661⟩,
⟨64,233620119,233620256⟩]
theorem checked52889 : checkPrefixCuts (2^48) 6936199169 10 Manual.Count131072.C052889.packed 64 cuts52889 = true := by
 decide +kernel
def pointBounds52889 : List (Nat × Nat × Nat) := [(6936293376,112355218881164,112355606400214)]
theorem point_links_checked52889 : (cuts52889.take 1).map (fun c => (6936199169-1+2*2^10*c.k,112355050797601+c.lower,112355438316553+c.upper)) = pointBounds52889 := by
 decide +kernel
def cuts52890 : List PrefixCut := [⟨64,234346148,234346277⟩]
theorem checked52890 : checkPrefixCuts (2^48) 6936330241 10 Manual.Count131072.C052890.packed 64 cuts52890 = true := by
 decide +kernel
def cuts52891 : List PrefixCut := [⟨24,88908348,88908398⟩,
⟨64,237628565,237628698⟩]
theorem checked52891 : checkPrefixCuts (2^48) 6936461313 10 Manual.Count131072.C052891.packed 64 cuts52891 = true := by
 decide +kernel
def pointBounds52891 : List (Nat × Nat × Nat) := [(6936510464,112355607672216,112355995191484)]
theorem point_links_checked52891 : (cuts52891.take 1).map (fun c => (6936461313-1+2*2^10*c.k,112355518763868+c.lower,112355906283086+c.upper)) = pointBounds52891 := by
 decide +kernel
def cuts52892 : List PrefixCut := [⟨64,235473469,235473606⟩]
theorem checked52892 : checkPrefixCuts (2^48) 6936592385 10 Manual.Count131072.C052892.packed 64 cuts52892 = true := by
 decide +kernel
def cuts52893 : List PrefixCut := [⟨2,7628567,7628572⟩,
⟨64,234738620,234738754⟩]
theorem checked52893 : checkPrefixCuts (2^48) 6936723457 10 Manual.Count131072.C052893.packed 64 cuts52893 = true := by
 decide +kernel
def pointBounds52893 : List (Nat × Nat × Nat) := [(6936727552,112355999494469,112356387013962)]
theorem point_links_checked52893 : (cuts52893.take 1).map (fun c => (6936723457-1+2*2^10*c.k,112355991865902+c.lower,112356379385390+c.upper)) = pointBounds52893 := by
 decide +kernel
def cuts52894 : List PrefixCut := [⟨44,160358206,160358299⟩,
⟨64,233111130,233111264⟩]
theorem checked52894 : checkPrefixCuts (2^48) 6936854529 10 Manual.Count131072.C052894.packed 64 cuts52894 = true := by
 decide +kernel
def pointBounds52894 : List (Nat × Nat × Nat) := [(6936944640,112356386962728,112356774482443)]
theorem point_links_checked52894 : (cuts52894.take 1).map (fun c => (6936854529-1+2*2^10*c.k,112356226604522+c.lower,112356614124144+c.upper)) = pointBounds52894 := by
 decide +kernel
def cuts52895 : List PrefixCut := [⟨64,233431342,233431473⟩]
theorem checked52895 : checkPrefixCuts (2^48) 6936985601 10 Manual.Count131072.C052895.packed 64 cuts52895 = true := by
 decide +kernel
def cuts52896 : List PrefixCut := [⟨22,80379209,80379256⟩,
⟨64,231519914,231520046⟩]
theorem checked52896 : checkPrefixCuts (2^48) 6937116673 10 Manual.Count131072.C052896.packed 64 cuts52896 = true := by
 decide +kernel
def pointBounds52896 : List (Nat × Nat × Nat) := [(6937161728,112356773526203,112357161046137)]
theorem point_links_checked52896 : (cuts52896.take 1).map (fun c => (6937116673-1+2*2^10*c.k,112356693146994+c.lower,112357080666881+c.upper)) = pointBounds52896 := by
 decide +kernel
def cuts52897 : List PrefixCut := [⟨64,234071694,234071833⟩]
theorem checked52897 : checkPrefixCuts (2^48) 6937247745 10 Manual.Count131072.C052897.packed 64 cuts52897 = true := by
 decide +kernel
def pointBounds52897 : List (Nat × Nat × Nat) := [(6937378816,112357158738602,112357546258760)]
theorem point_links_checked52897 : (cuts52897.take 1).map (fun c => (6937247745-1+2*2^10*c.k,112356924666908+c.lower,112357312186927+c.upper)) = pointBounds52897 := by
 decide +kernel
def cuts52898 : List PrefixCut := [⟨64,239341803,239341938⟩]
theorem checked52898 : checkPrefixCuts (2^48) 6937378817 10 Manual.Count131072.C052898.packed 64 cuts52898 = true := by
 decide +kernel
def cuts52899 : List PrefixCut := [⟨42,152350292,152350377⟩,
⟨64,235320575,235320706⟩]
theorem checked52899 : checkPrefixCuts (2^48) 6937509889 10 Manual.Count131072.C052899.packed 64 cuts52899 = true := by
 decide +kernel
def pointBounds52899 : List (Nat × Nat × Nat) := [(6937595904,112357550430697,112357937951075)]
theorem point_links_checked52899 : (cuts52899.take 1).map (fun c => (6937509889-1+2*2^10*c.k,112357398080405+c.lower,112357785600698+c.upper)) = pointBounds52899 := by
 decide +kernel
def cuts52900 : List PrefixCut := [⟨64,232192132,232192265⟩]
theorem checked52900 : checkPrefixCuts (2^48) 6937640961 10 Manual.Count131072.C052900.packed 64 cuts52900 = true := by
 decide +kernel
def cuts52901 : List PrefixCut := [⟨20,72987674,72987716⟩,
⟨64,234662568,234662703⟩]
theorem checked52901 : checkPrefixCuts (2^48) 6937772033 10 Manual.Count131072.C052901.packed 64 cuts52901 = true := by
 decide +kernel
def pointBounds52901 : List (Nat × Nat × Nat) := [(6937812992,112357938580786,112358326101385)]
theorem point_links_checked52901 : (cuts52901.take 1).map (fun c => (6937772033-1+2*2^10*c.k,112357865593112+c.lower,112358253113669+c.upper)) = pointBounds52901 := by
 decide +kernel
def cuts52902 : List PrefixCut := [⟨62,226909286,226909412⟩,
⟨64,234171288,234171419⟩]
theorem checked52902 : checkPrefixCuts (2^48) 6937903105 10 Manual.Count131072.C052902.packed 64 cuts52902 = true := by
 decide +kernel
def pointBounds52902 : List (Nat × Nat × Nat) := [(6938030080,112358327164966,112358714685784)]
theorem point_links_checked52902 : (cuts52902.take 1).map (fun c => (6937903105-1+2*2^10*c.k,112358100255680+c.lower,112358487776372+c.upper)) = pointBounds52902 := by
 decide +kernel
def cuts52903 : List PrefixCut := [⟨64,231976120,231976253⟩]
theorem checked52903 : checkPrefixCuts (2^48) 6938034177 10 Manual.Count131072.C052903.packed 64 cuts52903 = true := by
 decide +kernel
def cuts52904 : List PrefixCut := [⟨40,146818590,146818674⟩,
⟨64,235217234,235217366⟩]
theorem checked52904 : checkPrefixCuts (2^48) 6938165249 10 Manual.Count131072.C052904.packed 64 cuts52904 = true := by
 decide +kernel
def pointBounds52904 : List (Nat × Nat × Nat) := [(6938247168,112358713221678,112359100742718)]
theorem point_links_checked52904 : (cuts52904.take 1).map (fun c => (6938165249-1+2*2^10*c.k,112358566403088+c.lower,112358953924044+c.upper)) = pointBounds52904 := by
 decide +kernel
def cuts52905 : List PrefixCut := [⟨64,235375082,235375217⟩]
theorem checked52905 : checkPrefixCuts (2^48) 6938296321 10 Manual.Count131072.C052905.packed 64 cuts52905 = true := by
 decide +kernel
def cuts52906 : List PrefixCut := [⟨18,65272991,65273028⟩,
⟨64,234397002,234397137⟩]
theorem checked52906 : checkPrefixCuts (2^48) 6938427393 10 Manual.Count131072.C052906.packed 64 cuts52906 = true := by
 decide +kernel
def pointBounds52906 : List (Nat × Nat × Nat) := [(6938464256,112359102268395,112359489789655)]
theorem point_links_checked52906 : (cuts52906.take 1).map (fun c => (6938427393-1+2*2^10*c.k,112359036995404+c.lower,112359424516627+c.upper)) = pointBounds52906 := by
 decide +kernel
def cuts52907 : List PrefixCut := [⟨60,221654870,221654995⟩,
⟨64,237151092,237151226⟩]
theorem checked52907 : checkPrefixCuts (2^48) 6938558465 10 Manual.Count131072.C052907.packed 64 cuts52907 = true := by
 decide +kernel
def pointBounds52907 : List (Nat × Nat × Nat) := [(6938681344,112359493047276,112359880568759)]
theorem point_links_checked52907 : (cuts52907.take 1).map (fun c => (6938558465-1+2*2^10*c.k,112359271392406+c.lower,112359658913764+c.upper)) = pointBounds52907 := by
 decide +kernel
def cuts52908 : List PrefixCut := [⟨64,234874918,234875052⟩]
theorem checked52908 : checkPrefixCuts (2^48) 6938689537 10 Manual.Count131072.C052908.packed 64 cuts52908 = true := by
 decide +kernel
def cuts52909 : List PrefixCut := [⟨38,141653021,141653102⟩,
⟨64,237710048,237710182⟩]
theorem checked52909 : checkPrefixCuts (2^48) 6938820609 10 Manual.Count131072.C052909.packed 64 cuts52909 = true := by
 decide +kernel
def pointBounds52909 : List (Nat × Nat × Nat) := [(6938898432,112359885071437,112360272593144)]
theorem point_links_checked52909 : (cuts52909.take 1).map (fun c => (6938820609-1+2*2^10*c.k,112359743418416+c.lower,112360130940042+c.upper)) = pointBounds52909 := by
 decide +kernel
def cuts52910 : List PrefixCut := [⟨64,233243453,233243584⟩]
theorem checked52910 : checkPrefixCuts (2^48) 6938951681 10 Manual.Count131072.C052910.packed 64 cuts52910 = true := by
 decide +kernel
def cuts52911 : List PrefixCut := [⟨16,58249342,58249375⟩,
⟨64,236362470,236362601⟩]
theorem checked52911 : checkPrefixCuts (2^48) 6939082753 10 Manual.Count131072.C052911.packed 64 cuts52911 = true := by
 decide +kernel
def pointBounds52911 : List (Nat × Nat × Nat) := [(6939115520,112360272621259,112360660143183)]
theorem point_links_checked52911 : (cuts52911.take 1).map (fun c => (6939082753-1+2*2^10*c.k,112360214371917+c.lower,112360601893808+c.upper)) = pointBounds52911 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000090
