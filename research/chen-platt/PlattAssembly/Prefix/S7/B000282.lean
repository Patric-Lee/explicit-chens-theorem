import PlattAssemblyKernel
import PlattCertificates.Count131072.C069024
import PlattCertificates.Count131072.C069025
import PlattCertificates.Count131072.C069026
import PlattCertificates.Count131072.C069027
import PlattCertificates.Count131072.C069028
import PlattCertificates.Count131072.C069029
import PlattCertificates.Count131072.C069030
import PlattCertificates.Count131072.C069031
import PlattCertificates.Count131072.C069032
import PlattCertificates.Count131072.C069033
import PlattCertificates.Count131072.C069034
import PlattCertificates.Count131072.C069035
import PlattCertificates.Count131072.C069036
import PlattCertificates.Count131072.C069037
import PlattCertificates.Count131072.C069038
import PlattCertificates.Count131072.C069039
import PlattCertificates.Count131072.C069040
import PlattCertificates.Count131072.C069041
import PlattCertificates.Count131072.C069042
import PlattCertificates.Count131072.C069043
import PlattCertificates.Count131072.C069044
import PlattCertificates.Count131072.C069045
import PlattCertificates.Count131072.C069046
import PlattCertificates.Count131072.C069047
import PlattCertificates.Count131072.C069048
import PlattCertificates.Count131072.C069049
import PlattCertificates.Count131072.C069050
import PlattCertificates.Count131072.C069051
import PlattCertificates.Count131072.C069052
import PlattCertificates.Count131072.C069053
import PlattCertificates.Count131072.C069054
import PlattCertificates.Count131072.C069055
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000282
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts69024 : List PrefixCut := [⟨48,131390889,131390971⟩,
⟨64,175768035,175768143⟩]
theorem checked69024 : checkPrefixCuts (2^48) 9051045889 10 Manual.Count131072.C069024.packed 64 cuts69024 = true := by
 decide +kernel
def pointBounds69024 : List (Nat × Nat × Nat) := [(9051144192,115641628874150,115642018278150)]
theorem point_links_checked69024 : (cuts69024.take 1).map (fun c => (9051045889-1+2*2^10*c.k,115641497483261+c.lower,115641886887179+c.upper)) = pointBounds69024 := by
 decide +kernel
def cuts69025 : List PrefixCut := [⟨64,177973448,177973556⟩]
theorem checked69025 : checkPrefixCuts (2^48) 9051176961 10 Manual.Count131072.C069025.packed 64 cuts69025 = true := by
 decide +kernel
def cuts69026 : List PrefixCut := [⟨59,164630138,164630236⟩,
⟨64,178406229,178406335⟩]
theorem checked69026 : checkPrefixCuts (2^48) 9051308033 10 Manual.Count131072.C069026.packed 64 cuts69026 = true := by
 decide +kernel
def pointBounds69026 : List (Nat × Nat × Nat) := [(9051428864,115642015854882,115642405259114)]
theorem point_links_checked69026 : (cuts69026.take 1).map (fun c => (9051308033-1+2*2^10*c.k,115641851224744+c.lower,115642240628878+c.upper)) = pointBounds69026 := by
 decide +kernel
def cuts69027 : List PrefixCut := [⟨64,178434743,178434856⟩]
theorem checked69027 : checkPrefixCuts (2^48) 9051439105 10 Manual.Count131072.C069027.packed 64 cuts69027 = true := by
 decide +kernel
def cuts69028 : List PrefixCut := [⟨64,178898613,178898719⟩]
theorem checked69028 : checkPrefixCuts (2^48) 9051570177 10 Manual.Count131072.C069028.packed 64 cuts69028 = true := by
 decide +kernel
def cuts69029 : List PrefixCut := [⟨6,16729825,16729836⟩,
⟨64,178927126,178927233⟩]
theorem checked69029 : checkPrefixCuts (2^48) 9051701249 10 Manual.Count131072.C069029.packed 64 cuts69029 = true := by
 decide +kernel
def pointBounds69029 : List (Nat × Nat × Nat) := [(9051713536,115642403694154,115642793098624)]
theorem point_links_checked69029 : (cuts69029.take 1).map (fun c => (9051701249-1+2*2^10*c.k,115642386964329+c.lower,115642776368788+c.upper)) = pointBounds69029 := by
 decide +kernel
def cuts69030 : List PrefixCut := [⟨64,177276463,177276566⟩]
theorem checked69030 : checkPrefixCuts (2^48) 9051832321 10 Manual.Count131072.C069030.packed 64 cuts69030 = true := by
 decide +kernel
def cuts69031 : List PrefixCut := [⟨17,47296093,47296123⟩,
⟨64,178517706,178517810⟩]
theorem checked69031 : checkPrefixCuts (2^48) 9051963393 10 Manual.Count131072.C069031.packed 64 cuts69031 = true := by
 decide +kernel
def pointBounds69031 : List (Nat × Nat × Nat) := [(9051998208,115642790464011,115643179868710)]
theorem point_links_checked69031 : (cuts69031.take 1).map (fun c => (9051963393-1+2*2^10*c.k,115642743167918+c.lower,115643132572587+c.upper)) = pointBounds69031 := by
 decide +kernel
def cuts69032 : List PrefixCut := [⟨64,177053660,177053767⟩]
theorem checked69032 : checkPrefixCuts (2^48) 9052094465 10 Manual.Count131072.C069032.packed 64 cuts69032 = true := by
 decide +kernel
def cuts69033 : List PrefixCut := [⟨28,76865488,76865534⟩,
⟨64,175216529,175216633⟩]
theorem checked69033 : checkPrefixCuts (2^48) 9052225537 10 Manual.Count131072.C069033.packed 64 cuts69033 = true := by
 decide +kernel
def pointBounds69033 : List (Nat × Nat × Nat) := [(9052282880,115643175604772,115643565009698)]
theorem point_links_checked69033 : (cuts69033.take 1).map (fun c => (9052225537-1+2*2^10*c.k,115643098739284+c.lower,115643488144164+c.upper)) = pointBounds69033 := by
 decide +kernel
def cuts69034 : List PrefixCut := [⟨64,178105719,178105831⟩]
theorem checked69034 : checkPrefixCuts (2^48) 9052356609 10 Manual.Count131072.C069034.packed 64 cuts69034 = true := by
 decide +kernel
def cuts69035 : List PrefixCut := [⟨39,106059979,106060044⟩,
⟨64,174620679,174620789⟩]
theorem checked69035 : checkPrefixCuts (2^48) 9052487681 10 Manual.Count131072.C069035.packed 64 cuts69035 = true := by
 decide +kernel
def pointBounds69035 : List (Nat × Nat × Nat) := [(9052567552,115643558121511,115643947526672)]
theorem point_links_checked69035 : (cuts69035.take 1).map (fun c => (9052487681-1+2*2^10*c.k,115643452061532+c.lower,115643841466628+c.upper)) = pointBounds69035 := by
 decide +kernel
def cuts69036 : List PrefixCut := [⟨64,176701372,176701473⟩]
theorem checked69036 : checkPrefixCuts (2^48) 9052618753 10 Manual.Count131072.C069036.packed 64 cuts69036 = true := by
 decide +kernel
def cuts69037 : List PrefixCut := [⟨50,139885499,139885586⟩,
⟨64,178440013,178440121⟩]
theorem checked69037 : checkPrefixCuts (2^48) 9052749825 10 Manual.Count131072.C069037.packed 64 cuts69037 = true := by
 decide +kernel
def pointBounds69037 : List (Nat × Nat × Nat) := [(9052852224,115643943269082,115644332674476)]
theorem point_links_checked69037 : (cuts69037.take 1).map (fun c => (9052749825-1+2*2^10*c.k,115643803383583+c.lower,115644192788890+c.upper)) = pointBounds69037 := by
 decide +kernel
def cuts69038 : List PrefixCut := [⟨64,176913913,176914016⟩]
theorem checked69038 : checkPrefixCuts (2^48) 9052880897 10 Manual.Count131072.C069038.packed 64 cuts69038 = true := by
 decide +kernel
def cuts69039 : List PrefixCut := [⟨61,171035096,171035195⟩,
⟨64,179678508,179678612⟩]
theorem checked69039 : checkPrefixCuts (2^48) 9053011969 10 Manual.Count131072.C069039.packed 64 cuts69039 = true := by
 decide +kernel
def pointBounds69039 : List (Nat × Nat × Nat) := [(9053136896,115644329772605,115644719178222)]
theorem point_links_checked69039 : (cuts69039.take 1).map (fun c => (9053011969-1+2*2^10*c.k,115644158737509+c.lower,115644548143027+c.upper)) = pointBounds69039 := by
 decide +kernel
def cuts69040 : List PrefixCut := [⟨64,177437341,177437436⟩]
theorem checked69040 : checkPrefixCuts (2^48) 9053143041 10 Manual.Count131072.C069040.packed 64 cuts69040 = true := by
 decide +kernel
def cuts69041 : List PrefixCut := [⟨64,179611125,179611229⟩]
theorem checked69041 : checkPrefixCuts (2^48) 9053274113 10 Manual.Count131072.C069041.packed 64 cuts69041 = true := by
 decide +kernel
def cuts69042 : List PrefixCut := [⟨8,22696042,22696058⟩,
⟨64,176126424,176126525⟩]
theorem checked69042 : checkPrefixCuts (2^48) 9053405185 10 Manual.Count131072.C069042.packed 64 cuts69042 = true := by
 decide +kernel
def pointBounds69042 : List (Nat × Nat × Nat) := [(9053421568,115644718160525,115645107566362)]
theorem point_links_checked69042 : (cuts69042.take 1).map (fun c => (9053405185-1+2*2^10*c.k,115644695464483+c.lower,115645084870304+c.upper)) = pointBounds69042 := by
 decide +kernel
def cuts69043 : List PrefixCut := [⟨64,177180909,177181014⟩]
theorem checked69043 : checkPrefixCuts (2^48) 9053536257 10 Manual.Count131072.C069043.packed 64 cuts69043 = true := by
 decide +kernel
def cuts69044 : List PrefixCut := [⟨19,54562130,54562164⟩,
⟨64,178763914,178764025⟩]
theorem checked69044 : checkPrefixCuts (2^48) 9053667329 10 Manual.Count131072.C069044.packed 64 cuts69044 = true := by
 decide +kernel
def pointBounds69044 : List (Nat × Nat × Nat) := [(9053706240,115645103333946,115645492740007)]
theorem point_links_checked69044 : (cuts69044.take 1).map (fun c => (9053667329-1+2*2^10*c.k,115645048771816+c.lower,115645438177843+c.upper)) = pointBounds69044 := by
 decide +kernel
def cuts69045 : List PrefixCut := [⟨64,176149853,176149959⟩]
theorem checked69045 : checkPrefixCuts (2^48) 9053798401 10 Manual.Count131072.C069045.packed 64 cuts69045 = true := by
 decide +kernel
def cuts69046 : List PrefixCut := [⟨30,86084315,86084363⟩,
⟨64,179598122,179598229⟩]
theorem checked69046 : checkPrefixCuts (2^48) 9053929473 10 Manual.Count131072.C069046.packed 64 cuts69046 = true := by
 decide +kernel
def pointBounds69046 : List (Nat × Nat × Nat) := [(9053990912,115645489769898,115645879176190)]
theorem point_links_checked69046 : (cuts69046.take 1).map (fun c => (9053929473-1+2*2^10*c.k,115645403685583+c.lower,115645793091827+c.upper)) = pointBounds69046 := by
 decide +kernel
def cuts69047 : List PrefixCut := [⟨64,179315739,179315841⟩]
theorem checked69047 : checkPrefixCuts (2^48) 9054060545 10 Manual.Count131072.C069047.packed 64 cuts69047 = true := by
 decide +kernel
def cuts69048 : List PrefixCut := [⟨41,109801593,109801659⟩,
⟨64,173655176,173655279⟩]
theorem checked69048 : checkPrefixCuts (2^48) 9054191617 10 Manual.Count131072.C069048.packed 64 cuts69048 = true := by
 decide +kernel
def pointBounds69048 : List (Nat × Nat × Nat) := [(9054275584,115645872401037,115646261807556)]
theorem point_links_checked69048 : (cuts69048.take 1).map (fun c => (9054191617-1+2*2^10*c.k,115645762599444+c.lower,115646152005897+c.upper)) = pointBounds69048 := by
 decide +kernel
def cuts69049 : List PrefixCut := [⟨64,180180974,180181080⟩]
theorem checked69049 : checkPrefixCuts (2^48) 9054322689 10 Manual.Count131072.C069049.packed 64 cuts69049 = true := by
 decide +kernel
def cuts69050 : List PrefixCut := [⟨52,144242362,144242448⟩,
⟨64,178375330,178375436⟩]
theorem checked69050 : checkPrefixCuts (2^48) 9054453761 10 Manual.Count131072.C069050.packed 64 cuts69050 = true := by
 decide +kernel
def pointBounds69050 : List (Nat × Nat × Nat) := [(9054560256,115646260677956,115646650084704)]
theorem point_links_checked69050 : (cuts69050.take 1).map (fun c => (9054453761-1+2*2^10*c.k,115646116435594+c.lower,115646505842256+c.upper)) = pointBounds69050 := by
 decide +kernel
def cuts69051 : List PrefixCut := [⟨64,177657778,177657887⟩]
theorem checked69051 : checkPrefixCuts (2^48) 9054584833 10 Manual.Count131072.C069051.packed 64 cuts69051 = true := by
 decide +kernel
def cuts69052 : List PrefixCut := [⟨63,174702081,174702180⟩,
⟨64,177561952,177562053⟩]
theorem checked69052 : checkPrefixCuts (2^48) 9054715905 10 Manual.Count131072.C069052.packed 64 cuts69052 = true := by
 decide +kernel
def pointBounds69052 : List (Nat × Nat × Nat) := [(9054844928,115646647170783,115647036577759)]
theorem point_links_checked69052 : (cuts69052.take 1).map (fun c => (9054715905-1+2*2^10*c.k,115646472468702+c.lower,115646861875579+c.upper)) = pointBounds69052 := by
 decide +kernel
def cuts69053 : List PrefixCut := [⟨64,177528291,177528397⟩]
theorem checked69053 : checkPrefixCuts (2^48) 9054846977 10 Manual.Count131072.C069053.packed 64 cuts69053 = true := by
 decide +kernel
def cuts69054 : List PrefixCut := [⟨64,179266464,179266572⟩]
theorem checked69054 : checkPrefixCuts (2^48) 9054978049 10 Manual.Count131072.C069054.packed 64 cuts69054 = true := by
 decide +kernel
def cuts69055 : List PrefixCut := [⟨10,29126284,29126301⟩,
⟨64,181843889,181843998⟩]
theorem checked69055 : checkPrefixCuts (2^48) 9055109121 10 Manual.Count131072.C069055.packed 64 cuts69055 = true := by
 decide +kernel
def pointBounds69055 : List (Nat × Nat × Nat) := [(9055129600,115647035951693,115647425358902)]
theorem point_links_checked69055 : (cuts69055.take 1).map (fun c => (9055109121-1+2*2^10*c.k,115647006825409+c.lower,115647396232601+c.upper)) = pointBounds69055 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000282
