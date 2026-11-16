import PlattAssemblyKernel
import PlattCertificates.Count131072.C076016
import PlattCertificates.Count131072.C076017
import PlattCertificates.Count131072.C076018
import PlattCertificates.Count131072.C076019
import PlattCertificates.Count131072.C076020
import PlattCertificates.Count131072.C076021
import PlattCertificates.Count131072.C076022
import PlattCertificates.Count131072.C076023
import PlattCertificates.Count131072.C076024
import PlattCertificates.Count131072.C076025
import PlattCertificates.Count131072.C076026
import PlattCertificates.Count131072.C076027
import PlattCertificates.Count131072.C076028
import PlattCertificates.Count131072.C076029
import PlattCertificates.Count131072.C076030
import PlattCertificates.Count131072.C076031
import PlattCertificates.Count131072.C076032
import PlattCertificates.Count131072.C076033
import PlattCertificates.Count131072.C076034
import PlattCertificates.Count131072.C076035
import PlattCertificates.Count131072.C076036
import PlattCertificates.Count131072.C076037
import PlattCertificates.Count131072.C076038
import PlattCertificates.Count131072.C076039
import PlattCertificates.Count131072.C076040
import PlattCertificates.Count131072.C076041
import PlattCertificates.Count131072.C076042
import PlattCertificates.Count131072.C076043
import PlattCertificates.Count131072.C076044
import PlattCertificates.Count131072.C076045
import PlattCertificates.Count131072.C076046
import PlattCertificates.Count131072.C076047
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000188
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts76016 : List PrefixCut := [⟨64,161951107,161951210⟩]
theorem checked76016 : checkPrefixCuts (2^48) 9967501313 10 Manual.Count131072.C076016.packed 64 cuts76016 = true := by
 decide +kernel
def cuts76017 : List PrefixCut := [⟨14,34987936,34987956⟩,
⟨64,161412446,161412537⟩]
theorem checked76017 : checkPrefixCuts (2^48) 9967632385 10 Manual.Count131072.C076017.packed 64 cuts76017 = true := by
 decide +kernel
def pointBounds76017 : List (Nat × Nat × Nat) := [(9967661056,116823413259680,116823803366078)]
theorem point_links_checked76017 : (cuts76017.take 1).map (fun c => (9967632385-1+2*2^10*c.k,116823378271744+c.lower,116823768378122+c.upper)) = pointBounds76017 := by
 decide +kernel
def cuts76018 : List PrefixCut := [⟨64,161579751,161579850⟩]
theorem checked76018 : checkPrefixCuts (2^48) 9967763457 10 Manual.Count131072.C076018.packed 64 cuts76018 = true := by
 decide +kernel
def cuts76019 : List PrefixCut := [⟨39,97844799,97844858⟩,
⟨64,161379959,161380061⟩]
theorem checked76019 : checkPrefixCuts (2^48) 9967894529 10 Manual.Count131072.C076019.packed 64 cuts76019 = true := by
 decide +kernel
def pointBounds76019 : List (Nat × Nat × Nat) := [(9967974400,116823799108740,116824189215367)]
theorem point_links_checked76019 : (cuts76019.take 1).map (fun c => (9967894529-1+2*2^10*c.k,116823701263941+c.lower,116824091370509+c.upper)) = pointBounds76019 := by
 decide +kernel
def cuts76020 : List PrefixCut := [⟨64,160474236,160474333⟩]
theorem checked76020 : checkPrefixCuts (2^48) 9968025601 10 Manual.Count131072.C076020.packed 64 cuts76020 = true := by
 decide +kernel
def cuts76021 : List PrefixCut := [⟨64,159512071,159512168⟩]
theorem checked76021 : checkPrefixCuts (2^48) 9968156673 10 Manual.Count131072.C076021.packed 64 cuts76021 = true := by
 decide +kernel
def pointBounds76021 : List (Nat × Nat × Nat) := [(9968287744,116824182630207,116824572737071)]
theorem point_links_checked76021 : (cuts76021.take 1).map (fun c => (9968156673-1+2*2^10*c.k,116824023118136+c.lower,116824413224903+c.upper)) = pointBounds76021 := by
 decide +kernel
def cuts76022 : List PrefixCut := [⟨64,160808852,160808952⟩]
theorem checked76022 : checkPrefixCuts (2^48) 9968287745 10 Manual.Count131072.C076022.packed 64 cuts76022 = true := by
 decide +kernel
def cuts76023 : List PrefixCut := [⟨64,161089111,161089210⟩]
theorem checked76023 : checkPrefixCuts (2^48) 9968418817 10 Manual.Count131072.C076023.packed 64 cuts76023 = true := by
 decide +kernel
def cuts76024 : List PrefixCut := [⟨25,61978500,61978542⟩,
⟨64,160239905,160240004⟩]
theorem checked76024 : checkPrefixCuts (2^48) 9968549889 10 Manual.Count131072.C076024.packed 64 cuts76024 = true := by
 decide +kernel
def pointBounds76024 : List (Nat × Nat × Nat) := [(9968601088,116824566506670,116824956613775)]
theorem point_links_checked76024 : (cuts76024.take 1).map (fun c => (9968549889-1+2*2^10*c.k,116824504528170+c.lower,116824894635233+c.upper)) = pointBounds76024 := by
 decide +kernel
def cuts76025 : List PrefixCut := [⟨64,160040150,160040246⟩]
theorem checked76025 : checkPrefixCuts (2^48) 9968680961 10 Manual.Count131072.C076025.packed 64 cuts76025 = true := by
 decide +kernel
def cuts76026 : List PrefixCut := [⟨50,125704022,125704100⟩,
⟨64,160518048,160518147⟩]
theorem checked76026 : checkPrefixCuts (2^48) 9968812033 10 Manual.Count131072.C076026.packed 64 cuts76026 = true := by
 decide +kernel
def pointBounds76026 : List (Nat × Nat × Nat) := [(9968914432,116824950512247,116825340619583)]
theorem point_links_checked76026 : (cuts76026.take 1).map (fun c => (9968812033-1+2*2^10*c.k,116824824808225+c.lower,116825214915483+c.upper)) = pointBounds76026 := by
 decide +kernel
def cuts76027 : List PrefixCut := [⟨64,163000618,163000703⟩]
theorem checked76027 : checkPrefixCuts (2^48) 9968943105 10 Manual.Count131072.C076027.packed 64 cuts76027 = true := by
 decide +kernel
def cuts76028 : List PrefixCut := [⟨64,160654994,160655092⟩]
theorem checked76028 : checkPrefixCuts (2^48) 9969074177 10 Manual.Count131072.C076028.packed 64 cuts76028 = true := by
 decide +kernel
def cuts76029 : List PrefixCut := [⟨11,27387373,27387391⟩,
⟨64,160539952,160540056⟩]
theorem checked76029 : checkPrefixCuts (2^48) 9969205249 10 Manual.Count131072.C076029.packed 64 cuts76029 = true := by
 decide +kernel
def pointBounds76029 : List (Nat × Nat × Nat) := [(9969227776,116825336369258,116825726476816)]
theorem point_links_checked76029 : (cuts76029.take 1).map (fun c => (9969205249-1+2*2^10*c.k,116825308981885+c.lower,116825699089425+c.upper)) = pointBounds76029 := by
 decide +kernel
def cuts76030 : List PrefixCut := [⟨64,162514217,162514316⟩]
theorem checked76030 : checkPrefixCuts (2^48) 9969336321 10 Manual.Count131072.C076030.packed 64 cuts76030 = true := by
 decide +kernel
def cuts76031 : List PrefixCut := [⟨36,89952219,89952272⟩,
⟨64,161128628,161128726⟩]
theorem checked76031 : checkPrefixCuts (2^48) 9969467393 10 Manual.Count131072.C076031.packed 64 cuts76031 = true := by
 decide +kernel
def pointBounds76031 : List (Nat × Nat × Nat) := [(9969541120,116825721988273,116826112096069)]
theorem point_links_checked76031 : (cuts76031.take 1).map (fun c => (9969467393-1+2*2^10*c.k,116825632036054+c.lower,116826022143797+c.upper)) = pointBounds76031 := by
 decide +kernel
def cuts76032 : List PrefixCut := [⟨64,162227598,162227694⟩]
theorem checked76032 : checkPrefixCuts (2^48) 9969598465 10 Manual.Count131072.C076032.packed 64 cuts76032 = true := by
 decide +kernel
def cuts76033 : List PrefixCut := [⟨61,153219268,153219361⟩,
⟨64,160616206,160616304⟩]
theorem checked76033 : checkPrefixCuts (2^48) 9969729537 10 Manual.Count131072.C076033.packed 64 cuts76033 = true := by
 decide +kernel
def pointBounds76033 : List (Nat × Nat × Nat) := [(9969854464,116826108611548,116826498719578)]
theorem point_links_checked76033 : (cuts76033.take 1).map (fun c => (9969729537-1+2*2^10*c.k,116825955392280+c.lower,116826345500217+c.upper)) = pointBounds76033 := by
 decide +kernel
def cuts76034 : List PrefixCut := [⟨64,161573994,161574096⟩]
theorem checked76034 : checkPrefixCuts (2^48) 9969860609 10 Manual.Count131072.C076034.packed 64 cuts76034 = true := by
 decide +kernel
def cuts76035 : List PrefixCut := [⟨64,159877953,159878044⟩]
theorem checked76035 : checkPrefixCuts (2^48) 9969991681 10 Manual.Count131072.C076035.packed 64 cuts76035 = true := by
 decide +kernel
def cuts76036 : List PrefixCut := [⟨22,55560134,55560166⟩,
⟨64,159904091,159904184⟩]
theorem checked76036 : checkPrefixCuts (2^48) 9970122753 10 Manual.Count131072.C076036.packed 64 cuts76036 = true := by
 decide +kernel
def pointBounds76036 : List (Nat × Nat × Nat) := [(9970167808,116826493020567,116826883128827)]
theorem point_links_checked76036 : (cuts76036.take 1).map (fun c => (9970122753-1+2*2^10*c.k,116826437460433+c.lower,116826827568661+c.upper)) = pointBounds76036 := by
 decide +kernel
def cuts76037 : List PrefixCut := [⟨64,162950948,162951046⟩]
theorem checked76037 : checkPrefixCuts (2^48) 9970253825 10 Manual.Count131072.C076037.packed 64 cuts76037 = true := by
 decide +kernel
def cuts76038 : List PrefixCut := [⟨47,118146571,118146645⟩,
⟨64,160012807,160012908⟩]
theorem checked76038 : checkPrefixCuts (2^48) 9970384897 10 Manual.Count131072.C076038.packed 64 cuts76038 = true := by
 decide +kernel
def pointBounds76038 : List (Nat × Nat × Nat) := [(9970481152,116826878462043,116827268570536)]
theorem point_links_checked76038 : (cuts76038.take 1).map (fun c => (9970384897-1+2*2^10*c.k,116826760315472+c.lower,116827150423891+c.upper)) = pointBounds76038 := by
 decide +kernel
def cuts76039 : List PrefixCut := [⟨64,160660002,160660095⟩]
theorem checked76039 : checkPrefixCuts (2^48) 9970515969 10 Manual.Count131072.C076039.packed 64 cuts76039 = true := by
 decide +kernel
def cuts76040 : List PrefixCut := [⟨64,161053101,161053196⟩]
theorem checked76040 : checkPrefixCuts (2^48) 9970647041 10 Manual.Count131072.C076040.packed 64 cuts76040 = true := by
 decide +kernel
def cuts76041 : List PrefixCut := [⟨8,19478671,19478685⟩,
⟨64,157268190,157268287⟩]
theorem checked76041 : checkPrefixCuts (2^48) 9970778113 10 Manual.Count131072.C076041.packed 64 cuts76041 = true := by
 decide +kernel
def pointBounds76041 : List (Nat × Nat × Nat) := [(9970794496,116827261520053,116827651628775)]
theorem point_links_checked76041 : (cuts76041.take 1).map (fun c => (9970778113-1+2*2^10*c.k,116827242041382+c.lower,116827632150090+c.upper)) = pointBounds76041 := by
 decide +kernel
def cuts76042 : List PrefixCut := [⟨64,160399593,160399696⟩]
theorem checked76042 : checkPrefixCuts (2^48) 9970909185 10 Manual.Count131072.C076042.packed 64 cuts76042 = true := by
 decide +kernel
def cuts76043 : List PrefixCut := [⟨33,82908998,82909043⟩,
⟨64,161780710,161780801⟩]
theorem checked76043 : checkPrefixCuts (2^48) 9971040257 10 Manual.Count131072.C076043.packed 64 cuts76043 = true := by
 decide +kernel
def pointBounds76043 : List (Nat × Nat × Nat) := [(9971107840,116827642618163,116828032727116)]
theorem point_links_checked76043 : (cuts76043.take 1).map (fun c => (9971040257-1+2*2^10*c.k,116827559709165+c.lower,116827949818073+c.upper)) = pointBounds76043 := by
 decide +kernel
def cuts76044 : List PrefixCut := [⟨64,160480068,160480165⟩]
theorem checked76044 : checkPrefixCuts (2^48) 9971171329 10 Manual.Count131072.C076044.packed 64 cuts76044 = true := by
 decide +kernel
def cuts76045 : List PrefixCut := [⟨58,147069595,147069683⟩,
⟨64,162962041,162962137⟩]
theorem checked76045 : checkPrefixCuts (2^48) 9971302401 10 Manual.Count131072.C076045.packed 64 cuts76045 = true := by
 decide +kernel
def pointBounds76045 : List (Nat × Nat × Nat) := [(9971421184,116828029039538,116828419148722)]
theorem point_links_checked76045 : (cuts76045.take 1).map (fun c => (9971302401-1+2*2^10*c.k,116827881969943+c.lower,116828272079039+c.upper)) = pointBounds76045 := by
 decide +kernel
def cuts76046 : List PrefixCut := [⟨64,161576740,161576840⟩]
theorem checked76046 : checkPrefixCuts (2^48) 9971433473 10 Manual.Count131072.C076046.packed 64 cuts76046 = true := by
 decide +kernel
def cuts76047 : List PrefixCut := [⟨64,161489929,161490021⟩]
theorem checked76047 : checkPrefixCuts (2^48) 9971564545 10 Manual.Count131072.C076047.packed 64 cuts76047 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000188
