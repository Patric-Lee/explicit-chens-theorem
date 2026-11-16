import PlattAssemblyKernel
import PlattCertificates.Count131072.C050864
import PlattCertificates.Count131072.C050865
import PlattCertificates.Count131072.C050866
import PlattCertificates.Count131072.C050867
import PlattCertificates.Count131072.C050868
import PlattCertificates.Count131072.C050869
import PlattCertificates.Count131072.C050870
import PlattCertificates.Count131072.C050871
import PlattCertificates.Count131072.C050872
import PlattCertificates.Count131072.C050873
import PlattCertificates.Count131072.C050874
import PlattCertificates.Count131072.C050875
import PlattCertificates.Count131072.C050876
import PlattCertificates.Count131072.C050877
import PlattCertificates.Count131072.C050878
import PlattCertificates.Count131072.C050879
import PlattCertificates.Count131072.C050880
import PlattCertificates.Count131072.C050881
import PlattCertificates.Count131072.C050882
import PlattCertificates.Count131072.C050883
import PlattCertificates.Count131072.C050884
import PlattCertificates.Count131072.C050885
import PlattCertificates.Count131072.C050886
import PlattCertificates.Count131072.C050887
import PlattCertificates.Count131072.C050888
import PlattCertificates.Count131072.C050889
import PlattCertificates.Count131072.C050890
import PlattCertificates.Count131072.C050891
import PlattCertificates.Count131072.C050892
import PlattCertificates.Count131072.C050893
import PlattCertificates.Count131072.C050894
import PlattCertificates.Count131072.C050895
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000027
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts50864 : List PrefixCut := [⟨8,32110516,32110534⟩,
⟨64,249624418,249624559⟩]
theorem checked50864 : checkPrefixCuts (2^48) 6670778369 10 Manual.Count131072.C050864.packed 64 cuts50864 = true := by
 decide +kernel
def pointBounds50864 : List (Nat × Nat × Nat) := [(6670794752,111870036839438,111870424082789)]
theorem point_links_checked50864 : (cuts50864.take 1).map (fun c => (6670778369-1+2*2^10*c.k,111870004728922+c.lower,111870391972255+c.upper)) = pointBounds50864 := by
 decide +kernel
def cuts50865 : List PrefixCut := [⟨46,172869141,172869244⟩,
⟨64,240969723,240969865⟩]
theorem checked50865 : checkPrefixCuts (2^48) 6670909441 10 Manual.Count131072.C050865.packed 64 cuts50865 = true := by
 decide +kernel
def pointBounds50865 : List (Nat × Nat × Nat) := [(6671003648,111870427222481,111870814466058)]
theorem point_links_checked50865 : (cuts50865.take 1).map (fun c => (6670909441-1+2*2^10*c.k,111870254353340+c.lower,111870641596814+c.upper)) = pointBounds50865 := by
 decide +kernel
def cuts50866 : List PrefixCut := [⟨64,245310921,245311062⟩]
theorem checked50866 : checkPrefixCuts (2^48) 6671040513 10 Manual.Count131072.C050866.packed 64 cuts50866 = true := by
 decide +kernel
def cuts50867 : List PrefixCut := [⟨20,77676566,77676609⟩,
⟨64,248259558,248259700⟩]
theorem checked50867 : checkPrefixCuts (2^48) 6671171585 10 Manual.Count131072.C050867.packed 64 cuts50867 = true := by
 decide +kernel
def pointBounds50867 : List (Nat × Nat × Nat) := [(6671212544,111870818310550,111871205554350)]
theorem point_links_checked50867 : (cuts50867.take 1).map (fun c => (6671171585-1+2*2^10*c.k,111870740633984+c.lower,111871127877741+c.upper)) = pointBounds50867 := by
 decide +kernel
def cuts50868 : List PrefixCut := [⟨58,221378905,221379034⟩,
⟨64,244963733,244963875⟩]
theorem checked50868 : checkPrefixCuts (2^48) 6671302657 10 Manual.Count131072.C050868.packed 64 cuts50868 = true := by
 decide +kernel
def pointBounds50868 : List (Nat × Nat × Nat) := [(6671421440,111871210272447,111871597516475)]
theorem point_links_checked50868 : (cuts50868.take 1).map (fun c => (6671302657-1+2*2^10*c.k,111870988893542+c.lower,111871376137441+c.upper)) = pointBounds50868 := by
 decide +kernel
def cuts50869 : List PrefixCut := [⟨64,243693187,243693328⟩]
theorem checked50869 : checkPrefixCuts (2^48) 6671433729 10 Manual.Count131072.C050869.packed 64 cuts50869 = true := by
 decide +kernel
def cuts50870 : List PrefixCut := [⟨32,121591670,121591737⟩,
⟨64,240819523,240819658⟩]
theorem checked50870 : checkPrefixCuts (2^48) 6671564801 10 Manual.Count131072.C050870.packed 64 cuts50870 = true := by
 decide +kernel
def pointBounds50870 : List (Nat × Nat × Nat) := [(6671630336,111871599142132,111871986386381)]
theorem point_links_checked50870 : (cuts50870.take 1).map (fun c => (6671564801-1+2*2^10*c.k,111871477550462+c.lower,111871864794644+c.upper)) = pointBounds50870 := by
 decide +kernel
def cuts50871 : List PrefixCut := [⟨64,243177369,243177506⟩]
theorem checked50871 : checkPrefixCuts (2^48) 6671695873 10 Manual.Count131072.C050871.packed 64 cuts50871 = true := by
 decide +kernel
def cuts50872 : List PrefixCut := [⟨6,22950566,22950579⟩,
⟨64,245155431,245155570⟩]
theorem checked50872 : checkPrefixCuts (2^48) 6671826945 10 Manual.Count131072.C050872.packed 64 cuts50872 = true := by
 decide +kernel
def pointBounds50872 : List (Nat × Nat × Nat) := [(6671839232,111871984497920,111872371742387)]
theorem point_links_checked50872 : (cuts50872.take 1).map (fun c => (6671826945-1+2*2^10*c.k,111871961547354+c.lower,111872348791808+c.upper)) = pointBounds50872 := by
 decide +kernel
def cuts50873 : List PrefixCut := [⟨44,166893627,166893720⟩,
⟨64,243083442,243083578⟩]
theorem checked50873 : checkPrefixCuts (2^48) 6671958017 10 Manual.Count131072.C050873.packed 64 cuts50873 = true := by
 decide +kernel
def pointBounds50873 : List (Nat × Nat × Nat) := [(6672048128,111872373596412,111872760841098)]
theorem point_links_checked50873 : (cuts50873.take 1).map (fun c => (6671958017-1+2*2^10*c.k,111872206702785+c.lower,111872593947378+c.upper)) = pointBounds50873 := by
 decide +kernel
def cuts50874 : List PrefixCut := [⟨64,243078636,243078778⟩]
theorem checked50874 : checkPrefixCuts (2^48) 6672089089 10 Manual.Count131072.C050874.packed 64 cuts50874 = true := by
 decide +kernel
def cuts50875 : List PrefixCut := [⟨18,66653842,66653881⟩,
⟨64,244634722,244634863⟩]
theorem checked50875 : checkPrefixCuts (2^48) 6672220161 10 Manual.Count131072.C050875.packed 64 cuts50875 = true := by
 decide +kernel
def pointBounds50875 : List (Nat × Nat × Nat) := [(6672257024,111872759518705,111873146763615)]
theorem point_links_checked50875 : (cuts50875.take 1).map (fun c => (6672220161-1+2*2^10*c.k,111872692864863+c.lower,111873080109734+c.upper)) = pointBounds50875 := by
 decide +kernel
def cuts50876 : List PrefixCut := [⟨56,216661675,216661792⟩,
⟨64,247118873,247119009⟩]
theorem checked50876 : checkPrefixCuts (2^48) 6672351233 10 Manual.Count131072.C050876.packed 64 cuts50876 = true := by
 decide +kernel
def pointBounds50876 : List (Nat × Nat × Nat) := [(6672465920,111873154161260,111873541406389)]
theorem point_links_checked50876 : (cuts50876.take 1).map (fun c => (6672351233-1+2*2^10*c.k,111872937499585+c.lower,111873324744597+c.upper)) = pointBounds50876 := by
 decide +kernel
def cuts50877 : List PrefixCut := [⟨64,241883163,241883302⟩]
theorem checked50877 : checkPrefixCuts (2^48) 6672482305 10 Manual.Count131072.C050877.packed 64 cuts50877 = true := by
 decide +kernel
def cuts50878 : List PrefixCut := [⟨30,114232679,114232745⟩,
⟨64,245506172,245506316⟩]
theorem checked50878 : checkPrefixCuts (2^48) 6672613377 10 Manual.Count131072.C050878.packed 64 cuts50878 = true := by
 decide +kernel
def pointBounds50878 : List (Nat × Nat × Nat) := [(6672674816,111873540734300,111873927979653)]
theorem point_links_checked50878 : (cuts50878.take 1).map (fun c => (6672613377-1+2*2^10*c.k,111873426501621+c.lower,111873813746908+c.upper)) = pointBounds50878 := by
 decide +kernel
def cuts50879 : List PrefixCut := [⟨64,243139154,243139293⟩]
theorem checked50879 : checkPrefixCuts (2^48) 6672744449 10 Manual.Count131072.C050879.packed 64 cuts50879 = true := by
 decide +kernel
def cuts50880 : List PrefixCut := [⟨4,15522948,15522957⟩,
⟨64,245580900,245581041⟩]
theorem checked50880 : checkPrefixCuts (2^48) 6672875521 10 Manual.Count131072.C050880.packed 64 cuts50880 = true := by
 decide +kernel
def pointBounds50880 : List (Nat × Nat × Nat) := [(6672883712,111873930669895,111874317915474)]
theorem point_links_checked50880 : (cuts50880.take 1).map (fun c => (6672875521-1+2*2^10*c.k,111873915146947+c.lower,111874302392517+c.upper)) = pointBounds50880 := by
 decide +kernel
def cuts50881 : List PrefixCut := [⟨42,158895255,158895347⟩,
⟨64,240556571,240556712⟩]
theorem checked50881 : checkPrefixCuts (2^48) 6673006593 10 Manual.Count131072.C050881.packed 64 cuts50881 = true := by
 decide +kernel
def pointBounds50881 : List (Nat × Nat × Nat) := [(6673092608,111874319623102,111874706868905)]
theorem point_links_checked50881 : (cuts50881.take 1).map (fun c => (6673006593-1+2*2^10*c.k,111874160727847+c.lower,111874547973558+c.upper)) = pointBounds50881 := by
 decide +kernel
def cuts50882 : List PrefixCut := [⟨64,247131911,247132045⟩]
theorem checked50882 : checkPrefixCuts (2^48) 6673137665 10 Manual.Count131072.C050882.packed 64 cuts50882 = true := by
 decide +kernel
def cuts50883 : List PrefixCut := [⟨16,61455330,61455366⟩,
⟨64,247253587,247253728⟩]
theorem checked50883 : checkPrefixCuts (2^48) 6673268737 10 Manual.Count131072.C050883.packed 64 cuts50883 = true := by
 decide +kernel
def pointBounds50883 : List (Nat × Nat × Nat) := [(6673301504,111874709871659,111875097117681)]
theorem point_links_checked50883 : (cuts50883.take 1).map (fun c => (6673268737-1+2*2^10*c.k,111874648416329+c.lower,111875035662315+c.upper)) = pointBounds50883 := by
 decide +kernel
def cuts50884 : List PrefixCut := [⟨54,207264094,207264212⟩,
⟨64,245983381,245983521⟩]
theorem checked50884 : checkPrefixCuts (2^48) 6673399809 10 Manual.Count131072.C050884.packed 64 cuts50884 = true := by
 decide +kernel
def pointBounds50884 : List (Nat × Nat × Nat) := [(6673510400,111875102934010,111875490180255)]
theorem point_links_checked50884 : (cuts50884.take 1).map (fun c => (6673399809-1+2*2^10*c.k,111874895669916+c.lower,111875282916043+c.upper)) = pointBounds50884 := by
 decide +kernel
def cuts50885 : List PrefixCut := [⟨64,242351289,242351422⟩]
theorem checked50885 : checkPrefixCuts (2^48) 6673530881 10 Manual.Count131072.C050885.packed 64 cuts50885 = true := by
 decide +kernel
def cuts50886 : List PrefixCut := [⟨28,111262391,111262455⟩,
⟨64,247407751,247407893⟩]
theorem checked50886 : checkPrefixCuts (2^48) 6673661953 10 Manual.Count131072.C050886.packed 64 cuts50886 = true := by
 decide +kernel
def pointBounds50886 : List (Nat × Nat × Nat) := [(6673719296,111875495266977,111875882513441)]
theorem point_links_checked50886 : (cuts50886.take 1).map (fun c => (6673661953-1+2*2^10*c.k,111875384004586+c.lower,111875771250986+c.upper)) = pointBounds50886 := by
 decide +kernel
def cuts50887 : List PrefixCut := [⟨64,244703636,244703776⟩]
theorem checked50887 : checkPrefixCuts (2^48) 6673793025 10 Manual.Count131072.C050887.packed 64 cuts50887 = true := by
 decide +kernel
def cuts50888 : List PrefixCut := [⟨2,7760257,7760261⟩,
⟨64,243560089,243560225⟩]
theorem checked50888 : checkPrefixCuts (2^48) 6673924097 10 Manual.Count131072.C050888.packed 64 cuts50888 = true := by
 decide +kernel
def pointBounds50888 : List (Nat × Nat × Nat) := [(6673928192,111875883876230,111876271122916)]
theorem point_links_checked50888 : (cuts50888.take 1).map (fun c => (6673924097-1+2*2^10*c.k,111875876115973+c.lower,111876263362655+c.upper)) = pointBounds50888 := by
 decide +kernel
def cuts50889 : List PrefixCut := [⟨40,152712913,152713000⟩,
⟨64,246634013,246634151⟩]
theorem checked50889 : checkPrefixCuts (2^48) 6674055169 10 Manual.Count131072.C050889.packed 64 cuts50889 = true := by
 decide +kernel
def pointBounds50889 : List (Nat × Nat × Nat) := [(6674137088,111876272388975,111876659635880)]
theorem point_links_checked50889 : (cuts50889.take 1).map (fun c => (6674055169-1+2*2^10*c.k,111876119676062+c.lower,111876506922880+c.upper)) = pointBounds50889 := by
 decide +kernel
def cuts50890 : List PrefixCut := [⟨64,241821413,241821547⟩]
theorem checked50890 : checkPrefixCuts (2^48) 6674186241 10 Manual.Count131072.C050890.packed 64 cuts50890 = true := by
 decide +kernel
def cuts50891 : List PrefixCut := [⟨14,52968970,52968999⟩,
⟨64,244051805,244051944⟩]
theorem checked50891 : checkPrefixCuts (2^48) 6674317313 10 Manual.Count131072.C050891.packed 64 cuts50891 = true := by
 decide +kernel
def pointBounds50891 : List (Nat × Nat × Nat) := [(6674345984,111876661100458,111877048347577)]
theorem point_links_checked50891 : (cuts50891.take 1).map (fun c => (6674317313-1+2*2^10*c.k,111876608131488+c.lower,111876995378578+c.upper)) = pointBounds50891 := by
 decide +kernel
def cuts50892 : List PrefixCut := [⟨52,197995997,197996114⟩,
⟨64,241558908,241559049⟩]
theorem checked50892 : checkPrefixCuts (2^48) 6674448385 10 Manual.Count131072.C050892.packed 64 cuts50892 = true := by
 decide +kernel
def pointBounds50892 : List (Nat × Nat × Nat) := [(6674554880,111877050179290,111877437426636)]
theorem point_links_checked50892 : (cuts50892.take 1).map (fun c => (6674448385-1+2*2^10*c.k,111876852183293+c.lower,111877239430522+c.upper)) = pointBounds50892 := by
 decide +kernel
def cuts50893 : List PrefixCut := [⟨64,245897740,245897878⟩]
theorem checked50893 : checkPrefixCuts (2^48) 6674579457 10 Manual.Count131072.C050893.packed 64 cuts50893 = true := by
 decide +kernel
def cuts50894 : List PrefixCut := [⟨26,98130014,98130070⟩,
⟨64,241465064,241465201⟩]
theorem checked50894 : checkPrefixCuts (2^48) 6674710529 10 Manual.Count131072.C050894.packed 64 cuts50894 = true := by
 decide +kernel
def pointBounds50894 : List (Nat × Nat × Nat) := [(6674763776,111877437769955,111877825017519)]
theorem point_links_checked50894 : (cuts50894.take 1).map (fun c => (6674710529-1+2*2^10*c.k,111877339639941+c.lower,111877726887449+c.upper)) = pointBounds50894 := by
 decide +kernel
def cuts50895 : List PrefixCut := [⟨64,244074801,244074939⟩]
theorem checked50895 : checkPrefixCuts (2^48) 6674841601 10 Manual.Count131072.C050895.packed 64 cuts50895 = true := by
 decide +kernel
def pointBounds50895 : List (Nat × Nat × Nat) := [(6674972672,111877825179806,111878212427589)]
theorem point_links_checked50895 : (cuts50895.take 1).map (fun c => (6674841601-1+2*2^10*c.k,111877581105005+c.lower,111877968352650+c.upper)) = pointBounds50895 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000027
