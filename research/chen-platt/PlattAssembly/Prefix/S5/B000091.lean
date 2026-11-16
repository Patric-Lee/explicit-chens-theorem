import PlattAssemblyKernel
import PlattCertificates.Count131072.C042912
import PlattCertificates.Count131072.C042913
import PlattCertificates.Count131072.C042914
import PlattCertificates.Count131072.C042915
import PlattCertificates.Count131072.C042916
import PlattCertificates.Count131072.C042917
import PlattCertificates.Count131072.C042918
import PlattCertificates.Count131072.C042919
import PlattCertificates.Count131072.C042920
import PlattCertificates.Count131072.C042921
import PlattCertificates.Count131072.C042922
import PlattCertificates.Count131072.C042923
import PlattCertificates.Count131072.C042924
import PlattCertificates.Count131072.C042925
import PlattCertificates.Count131072.C042926
import PlattCertificates.Count131072.C042927
import PlattCertificates.Count131072.C042928
import PlattCertificates.Count131072.C042929
import PlattCertificates.Count131072.C042930
import PlattCertificates.Count131072.C042931
import PlattCertificates.Count131072.C042932
import PlattCertificates.Count131072.C042933
import PlattCertificates.Count131072.C042934
import PlattCertificates.Count131072.C042935
import PlattCertificates.Count131072.C042936
import PlattCertificates.Count131072.C042937
import PlattCertificates.Count131072.C042938
import PlattCertificates.Count131072.C042939
import PlattCertificates.Count131072.C042940
import PlattCertificates.Count131072.C042941
import PlattCertificates.Count131072.C042942
import PlattCertificates.Count131072.C042943
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000091
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts42912 : List PrefixCut := [⟨64,292098689,292098850⟩]
theorem checked42912 : checkPrefixCuts (2^48) 5628493825 10 Manual.Count131072.C042912.packed 64 cuts42912 = true := by
 decide +kernel
def cuts42913 : List PrefixCut := [⟨4,20303134,20303146⟩,
⟨64,296542575,296542742⟩]
theorem checked42913 : checkPrefixCuts (2^48) 5628624897 10 Manual.Count131072.C042913.packed 64 cuts42913 = true := by
 decide +kernel
def pointBounds42913 : List (Nat × Nat × Nat) := [(5628633088,109748312911435,109748698936086)]
theorem point_links_checked42913 : (cuts42913.take 1).map (fun c => (5628624897-1+2*2^10*c.k,109748292608301+c.lower,109748678632940+c.upper)) = pointBounds42913 := by
 decide +kernel
def cuts42914 : List PrefixCut := [⟨26,117464929,117464996⟩,
⟨64,291585038,291585207⟩]
theorem checked42914 : checkPrefixCuts (2^48) 5628755969 10 Manual.Count131072.C042914.packed 64 cuts42914 = true := by
 decide +kernel
def pointBounds42914 : List (Nat × Nat × Nat) := [(5628809216,109748706615805,109749092640678)]
theorem point_links_checked42914 : (cuts42914.take 1).map (fun c => (5628755969-1+2*2^10*c.k,109748589150876+c.lower,109748975175682+c.upper)) = pointBounds42914 := by
 decide +kernel
def cuts42915 : List PrefixCut := [⟨48,219171865,219171997⟩,
⟨64,291478242,291478414⟩]
theorem checked42915 : checkPrefixCuts (2^48) 5628887041 10 Manual.Count131072.C042915.packed 64 cuts42915 = true := by
 decide +kernel
def pointBounds42915 : List (Nat × Nat × Nat) := [(5628985344,109749099907779,109749485932886)]
theorem point_links_checked42915 : (cuts42915.take 1).map (fun c => (5628887041-1+2*2^10*c.k,109748880735914+c.lower,109749266760889+c.upper)) = pointBounds42915 := by
 decide +kernel
def cuts42916 : List PrefixCut := [⟨64,290071367,290071529⟩]
theorem checked42916 : checkPrefixCuts (2^48) 5629018113 10 Manual.Count131072.C042916.packed 64 cuts42916 = true := by
 decide +kernel
def cuts42917 : List PrefixCut := [⟨6,26951639,26951655⟩,
⟨64,291764648,291764813⟩]
theorem checked42917 : checkPrefixCuts (2^48) 5629149185 10 Manual.Count131072.C042917.packed 64 cuts42917 = true := by
 decide +kernel
def pointBounds42917 : List (Nat × Nat × Nat) := [(5629161472,109749489237162,109749875262487)]
theorem point_links_checked42917 : (cuts42917.take 1).map (fun c => (5629149185-1+2*2^10*c.k,109749462285523+c.lower,109749848310832+c.upper)) = pointBounds42917 := by
 decide +kernel
def cuts42918 : List PrefixCut := [⟨28,129354337,129354412⟩,
⟨64,295407976,295408144⟩]
theorem checked42918 : checkPrefixCuts (2^48) 5629280257 10 Manual.Count131072.C042918.packed 64 cuts42918 = true := by
 decide +kernel
def pointBounds42918 : List (Nat × Nat × Nat) := [(5629337600,109749883404508,109750269430057)]
theorem point_links_checked42918 : (cuts42918.take 1).map (fun c => (5629280257-1+2*2^10*c.k,109749754050171+c.lower,109750140075645+c.upper)) = pointBounds42918 := by
 decide +kernel
def cuts42919 : List PrefixCut := [⟨50,227601439,227601567⟩,
⟨64,290001103,290001268⟩]
theorem checked42919 : checkPrefixCuts (2^48) 5629411329 10 Manual.Count131072.C042919.packed 64 cuts42919 = true := by
 decide +kernel
def pointBounds42919 : List (Nat × Nat × Nat) := [(5629513728,109750277059586,109750663085356)]
theorem point_links_checked42919 : (cuts42919.take 1).map (fun c => (5629411329-1+2*2^10*c.k,109750049458147+c.lower,109750435483789+c.upper)) = pointBounds42919 := by
 decide +kernel
def cuts42920 : List PrefixCut := [⟨64,287594395,287594563⟩]
theorem checked42920 : checkPrefixCuts (2^48) 5629542401 10 Manual.Count131072.C042920.packed 64 cuts42920 = true := by
 decide +kernel
def cuts42921 : List PrefixCut := [⟨8,35748833,35748855⟩,
⟨64,294637336,294637507⟩]
theorem checked42921 : checkPrefixCuts (2^48) 5629673473 10 Manual.Count131072.C042921.packed 64 cuts42921 = true := by
 decide +kernel
def pointBounds42921 : List (Nat × Nat × Nat) := [(5629689856,109750662802478,109751048828475)]
theorem point_links_checked42921 : (cuts42921.take 1).map (fun c => (5629673473-1+2*2^10*c.k,109750627053645+c.lower,109751013079620+c.upper)) = pointBounds42921 := by
 decide +kernel
def cuts42922 : List PrefixCut := [⟨30,137641756,137641835⟩,
⟨64,296730373,296730542⟩]
theorem checked42922 : checkPrefixCuts (2^48) 5629804545 10 Manual.Count131072.C042922.packed 64 cuts42922 = true := by
 decide +kernel
def pointBounds42922 : List (Nat × Nat × Nat) := [(5629865984,109751059332737,109751445358962)]
theorem point_links_checked42922 : (cuts42922.take 1).map (fun c => (5629804545-1+2*2^10*c.k,109750921690981+c.lower,109751307717127+c.upper)) = pointBounds42922 := by
 decide +kernel
def cuts42923 : List PrefixCut := [⟨52,238079240,238079381⟩,
⟨64,294173696,294173870⟩]
theorem checked42923 : checkPrefixCuts (2^48) 5629935617 10 Manual.Count131072.C042923.packed 64 cuts42923 = true := by
 decide +kernel
def pointBounds42923 : List (Nat × Nat × Nat) := [(5630042112,109751456500594,109751842527050)]
theorem point_links_checked42923 : (cuts42923.take 1).map (fun c => (5629935617-1+2*2^10*c.k,109751218421354+c.lower,109751604447669+c.upper)) = pointBounds42923 := by
 decide +kernel
def cuts42924 : List PrefixCut := [⟨64,289767346,289767507⟩]
theorem checked42924 : checkPrefixCuts (2^48) 5630066689 10 Manual.Count131072.C042924.packed 64 cuts42924 = true := by
 decide +kernel
def cuts42925 : List PrefixCut := [⟨10,44944331,44944358⟩,
⟨64,290810467,290810637⟩]
theorem checked42925 : checkPrefixCuts (2^48) 5630197761 10 Manual.Count131072.C042925.packed 64 cuts42925 = true := by
 decide +kernel
def pointBounds42925 : List (Nat × Nat × Nat) := [(5630218240,109751847306727,109752233333404)]
theorem point_links_checked42925 : (cuts42925.take 1).map (fun c => (5630197761-1+2*2^10*c.k,109751802362396+c.lower,109752188389046+c.upper)) = pointBounds42925 := by
 decide +kernel
def cuts42926 : List PrefixCut := [⟨32,148077294,148077380⟩,
⟨64,291003703,291003873⟩]
theorem checked42926 : checkPrefixCuts (2^48) 5630328833 10 Manual.Count131072.C042926.packed 64 cuts42926 = true := by
 decide +kernel
def pointBounds42926 : List (Nat × Nat × Nat) := [(5630394368,109752241250157,109752627277063)]
theorem point_links_checked42926 : (cuts42926.take 1).map (fun c => (5630328833-1+2*2^10*c.k,109752093172863+c.lower,109752479199683+c.upper)) = pointBounds42926 := by
 decide +kernel
def cuts42927 : List PrefixCut := [⟨54,246505474,246505623⟩,
⟨64,291596801,291596980⟩]
theorem checked42927 : checkPrefixCuts (2^48) 5630459905 10 Manual.Count131072.C042927.packed 64 cuts42927 = true := by
 decide +kernel
def pointBounds42927 : List (Nat × Nat × Nat) := [(5630570496,109752630682040,109753016709179)]
theorem point_links_checked42927 : (cuts42927.take 1).map (fun c => (5630459905-1+2*2^10*c.k,109752384176566+c.lower,109752770203556+c.upper)) = pointBounds42927 := by
 decide +kernel
def cuts42928 : List PrefixCut := [⟨64,290890091,290890262⟩]
theorem checked42928 : checkPrefixCuts (2^48) 5630590977 10 Manual.Count131072.C042928.packed 64 cuts42928 = true := by
 decide +kernel
def cuts42929 : List PrefixCut := [⟨12,54887944,54887976⟩,
⟨64,294082597,294082766⟩]
theorem checked42929 : checkPrefixCuts (2^48) 5630722049 10 Manual.Count131072.C042929.packed 64 cuts42929 = true := by
 decide +kernel
def pointBounds42929 : List (Nat × Nat × Nat) := [(5630746624,109753021551402,109753407578774)]
theorem point_links_checked42929 : (cuts42929.take 1).map (fun c => (5630722049-1+2*2^10*c.k,109752966663458+c.lower,109753352690798+c.upper)) = pointBounds42929 := by
 decide +kernel
def cuts42930 : List PrefixCut := [⟨34,152462339,152462430⟩,
⟨64,288527144,288527316⟩]
theorem checked42930 : checkPrefixCuts (2^48) 5630853121 10 Manual.Count131072.C042930.packed 64 cuts42930 = true := by
 decide +kernel
def pointBounds42930 : List (Nat × Nat × Nat) := [(5630922752,109753413208394,109753799235994)]
theorem point_links_checked42930 : (cuts42930.take 1).map (fun c => (5630853121-1+2*2^10*c.k,109753260746055+c.lower,109753646773564+c.upper)) = pointBounds42930 := by
 decide +kernel
def cuts42931 : List PrefixCut := [⟨56,256829566,256829716⟩,
⟨64,293918965,293919136⟩]
theorem checked42931 : checkPrefixCuts (2^48) 5630984193 10 Manual.Count131072.C042931.packed 64 cuts42931 = true := by
 decide +kernel
def pointBounds42931 : List (Nat × Nat × Nat) := [(5631098880,109753806102765,109754192130596)]
theorem point_links_checked42931 : (cuts42931.take 1).map (fun c => (5630984193-1+2*2^10*c.k,109753549273199+c.lower,109753935300880+c.upper)) = pointBounds42931 := by
 decide +kernel
def cuts42932 : List PrefixCut := [⟨64,284564921,284565092⟩]
theorem checked42932 : checkPrefixCuts (2^48) 5631115265 10 Manual.Count131072.C042932.packed 64 cuts42932 = true := by
 decide +kernel
def cuts42933 : List PrefixCut := [⟨14,63430136,63430172⟩,
⟨64,293355462,293355628⟩]
theorem checked42933 : checkPrefixCuts (2^48) 5631246337 10 Manual.Count131072.C042933.packed 64 cuts42933 = true := by
 decide +kernel
def pointBounds42933 : List (Nat × Nat × Nat) := [(5631275008,109754191187221,109754577215280)]
theorem point_links_checked42933 : (cuts42933.take 1).map (fun c => (5631246337-1+2*2^10*c.k,109754127757085+c.lower,109754513785108+c.upper)) = pointBounds42933 := by
 decide +kernel
def cuts42934 : List PrefixCut := [⟨36,167792882,167792979⟩,
⟨64,295447936,295448103⟩]
theorem checked42934 : checkPrefixCuts (2^48) 5631377409 10 Manual.Count131072.C042934.packed 64 cuts42934 = true := by
 decide +kernel
def pointBounds42934 : List (Nat × Nat × Nat) := [(5631451136,109754588905429,109754974933715)]
theorem point_links_checked42934 : (cuts42934.take 1).map (fun c => (5631377409-1+2*2^10*c.k,109754421112547+c.lower,109754807140736+c.upper)) = pointBounds42934 := by
 decide +kernel
def cuts42935 : List PrefixCut := [⟨58,263603097,263603252⟩,
⟨64,290792783,290792954⟩]
theorem checked42935 : checkPrefixCuts (2^48) 5631508481 10 Manual.Count131072.C042935.packed 64 cuts42935 = true := by
 decide +kernel
def pointBounds42935 : List (Nat × Nat × Nat) := [(5631627264,109754980163580,109755366192091)]
theorem point_links_checked42935 : (cuts42935.take 1).map (fun c => (5631508481-1+2*2^10*c.k,109754716560483+c.lower,109755102588839+c.upper)) = pointBounds42935 := by
 decide +kernel
def cuts42936 : List PrefixCut := [⟨64,289786366,289786539⟩]
theorem checked42936 : checkPrefixCuts (2^48) 5631639553 10 Manual.Count131072.C042936.packed 64 cuts42936 = true := by
 decide +kernel
def cuts42937 : List PrefixCut := [⟨16,71470937,71470979⟩,
⟨64,285831271,285831436⟩]
theorem checked42937 : checkPrefixCuts (2^48) 5631770625 10 Manual.Count131072.C042937.packed 64 cuts42937 = true := by
 decide +kernel
def pointBounds42937 : List (Nat × Nat × Nat) := [(5631803392,109755368610569,109755754639311)]
theorem point_links_checked42937 : (cuts42937.take 1).map (fun c => (5631770625-1+2*2^10*c.k,109755297139632+c.lower,109755683168332+c.upper)) = pointBounds42937 := by
 decide +kernel
def cuts42938 : List PrefixCut := [⟨38,173124872,173124975⟩,
⟨64,293771106,293771282⟩]
theorem checked42938 : checkPrefixCuts (2^48) 5631901697 10 Manual.Count131072.C042938.packed 64 cuts42938 = true := by
 decide +kernel
def pointBounds42938 : List (Nat × Nat × Nat) := [(5631979520,109755756095775,109756142124743)]
theorem point_links_checked42938 : (cuts42938.take 1).map (fun c => (5631901697-1+2*2^10*c.k,109755582970903+c.lower,109755968999768+c.upper)) = pointBounds42938 := by
 decide +kernel
def cuts42939 : List PrefixCut := [⟨60,269875497,269875658⟩,
⟨64,287417203,287417374⟩]
theorem checked42939 : checkPrefixCuts (2^48) 5632032769 10 Manual.Count131072.C042939.packed 64 cuts42939 = true := by
 decide +kernel
def pointBounds42939 : List (Nat × Nat × Nat) := [(5632155648,109756146617506,109756532646708)]
theorem point_links_checked42939 : (cuts42939.take 1).map (fun c => (5632032769-1+2*2^10*c.k,109755876742009+c.lower,109756262771050+c.upper)) = pointBounds42939 := by
 decide +kernel
def cuts42940 : List PrefixCut := [⟨64,293207707,293207873⟩]
theorem checked42940 : checkPrefixCuts (2^48) 5632163841 10 Manual.Count131072.C042940.packed 64 cuts42940 = true := by
 decide +kernel
def cuts42941 : List PrefixCut := [⟨18,81459260,81459309⟩,
⟨64,291151916,291152089⟩]
theorem checked42941 : checkPrefixCuts (2^48) 5632294913 10 Manual.Count131072.C042941.packed 64 cuts42941 = true := by
 decide +kernel
def pointBounds42941 : List (Nat × Nat × Nat) := [(5632331776,109756538826179,109756924855606)]
theorem point_links_checked42941 : (cuts42941.take 1).map (fun c => (5632294913-1+2*2^10*c.k,109756457366919+c.lower,109756843396297+c.upper)) = pointBounds42941 := by
 decide +kernel
def cuts42942 : List PrefixCut := [⟨40,185352225,185352332⟩,
⟨64,292694373,292694537⟩]
theorem checked42942 : checkPrefixCuts (2^48) 5632425985 10 Manual.Count131072.C042942.packed 64 cuts42942 = true := by
 decide +kernel
def pointBounds42942 : List (Nat × Nat × Nat) := [(5632507904,109756933871060,109757319900718)]
theorem point_links_checked42942 : (cuts42942.take 1).map (fun c => (5632425985-1+2*2^10*c.k,109756748518835+c.lower,109757134548386+c.upper)) = pointBounds42942 := by
 decide +kernel
def cuts42943 : List PrefixCut := [⟨62,280944164,280944328⟩,
⟨64,289589268,289589437⟩]
theorem checked42943 : checkPrefixCuts (2^48) 5632557057 10 Manual.Count131072.C042943.packed 64 cuts42943 = true := by
 decide +kernel
def pointBounds42943 : List (Nat × Nat × Nat) := [(5632684032,109757322157372,109757708187251)]
theorem point_links_checked42943 : (cuts42943.take 1).map (fun c => (5632557057-1+2*2^10*c.k,109757041213208+c.lower,109757427242923+c.upper)) = pointBounds42943 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000091
