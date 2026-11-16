import PlattAssemblyKernel
import PlattCertificates.Count131072.C069920
import PlattCertificates.Count131072.C069921
import PlattCertificates.Count131072.C069922
import PlattCertificates.Count131072.C069923
import PlattCertificates.Count131072.C069924
import PlattCertificates.Count131072.C069925
import PlattCertificates.Count131072.C069926
import PlattCertificates.Count131072.C069927
import PlattCertificates.Count131072.C069928
import PlattCertificates.Count131072.C069929
import PlattCertificates.Count131072.C069930
import PlattCertificates.Count131072.C069931
import PlattCertificates.Count131072.C069932
import PlattCertificates.Count131072.C069933
import PlattCertificates.Count131072.C069934
import PlattCertificates.Count131072.C069935
import PlattCertificates.Count131072.C069936
import PlattCertificates.Count131072.C069937
import PlattCertificates.Count131072.C069938
import PlattCertificates.Count131072.C069939
import PlattCertificates.Count131072.C069940
import PlattCertificates.Count131072.C069941
import PlattCertificates.Count131072.C069942
import PlattCertificates.Count131072.C069943
import PlattCertificates.Count131072.C069944
import PlattCertificates.Count131072.C069945
import PlattCertificates.Count131072.C069946
import PlattCertificates.Count131072.C069947
import PlattCertificates.Count131072.C069948
import PlattCertificates.Count131072.C069949
import PlattCertificates.Count131072.C069950
import PlattCertificates.Count131072.C069951
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000310
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts69920 : List PrefixCut := [⟨38,105915437,105915499⟩,
⟨64,177845319,177845425⟩]
theorem checked69920 : checkPrefixCuts (2^48) 9168486401 10 Manual.Count131072.C069920.packed 64 cuts69920 = true := by
 decide +kernel
def pointBounds69920 : List (Nat × Nat × Nat) := [(9168564224,115799813176338,115800202673395)]
theorem point_links_checked69920 : (cuts69920.take 1).map (fun c => (9168486401-1+2*2^10*c.k,115799707260901+c.lower,115800096757896+c.upper)) = pointBounds69920 := by
 decide +kernel
def cuts69921 : List PrefixCut := [⟨64,173207140,173207243⟩]
theorem checked69921 : checkPrefixCuts (2^48) 9168617473 10 Manual.Count131072.C069921.packed 64 cuts69921 = true := by
 decide +kernel
def cuts69922 : List PrefixCut := [⟨50,134401136,134401216⟩,
⟨64,173112560,173112666⟩]
theorem checked69922 : checkPrefixCuts (2^48) 9168748545 10 Manual.Count131072.C069922.packed 64 cuts69922 = true := by
 decide +kernel
def pointBounds69922 : List (Nat × Nat × Nat) := [(9168850944,115800192714496,115800582211780)]
theorem point_links_checked69922 : (cuts69922.take 1).map (fun c => (9168748545-1+2*2^10*c.k,115800058313360+c.lower,115800447810564+c.upper)) = pointBounds69922 := by
 decide +kernel
def cuts69923 : List PrefixCut := [⟨64,173846864,173846964⟩]
theorem checked69923 : checkPrefixCuts (2^48) 9168879617 10 Manual.Count131072.C069923.packed 64 cuts69923 = true := by
 decide +kernel
def cuts69924 : List PrefixCut := [⟨62,168564292,168564391⟩,
⟨64,174458322,174458423⟩]
theorem checked69924 : checkPrefixCuts (2^48) 9169010689 10 Manual.Count131072.C069924.packed 64 cuts69924 = true := by
 decide +kernel
def pointBounds69924 : List (Nat × Nat × Nat) := [(9169137664,115800573837076,115800963334585)]
theorem point_links_checked69924 : (cuts69924.take 1).map (fun c => (9169010689-1+2*2^10*c.k,115800405272784+c.lower,115800794770194+c.upper)) = pointBounds69924 := by
 decide +kernel
def cuts69925 : List PrefixCut := [⟨64,172153514,172153621⟩]
theorem checked69925 : checkPrefixCuts (2^48) 9169141761 10 Manual.Count131072.C069925.packed 64 cuts69925 = true := by
 decide +kernel
def cuts69926 : List PrefixCut := [⟨64,175466373,175466476⟩]
theorem checked69926 : checkPrefixCuts (2^48) 9169272833 10 Manual.Count131072.C069926.packed 64 cuts69926 = true := by
 decide +kernel
def cuts69927 : List PrefixCut := [⟨10,26737219,26737234⟩,
⟨64,172731839,172731940⟩]
theorem checked69927 : checkPrefixCuts (2^48) 9169403905 10 Manual.Count131072.C069927.packed 64 cuts69927 = true := by
 decide +kernel
def pointBounds69927 : List (Nat × Nat × Nat) := [(9169424384,115800954088212,115801343585948)]
theorem point_links_checked69927 : (cuts69927.take 1).map (fun c => (9169403905-1+2*2^10*c.k,115800927350993+c.lower,115801316848714+c.upper)) = pointBounds69927 := by
 decide +kernel
def cuts69928 : List PrefixCut := [⟨64,175983191,175983297⟩]
theorem checked69928 : checkPrefixCuts (2^48) 9169534977 10 Manual.Count131072.C069928.packed 64 cuts69928 = true := by
 decide +kernel
def cuts69929 : List PrefixCut := [⟨22,61238983,61239020⟩,
⟨64,172450637,172450741⟩]
theorem checked69929 : checkPrefixCuts (2^48) 9169666049 10 Manual.Count131072.C069929.packed 64 cuts69929 = true := by
 decide +kernel
def pointBounds69929 : List (Nat × Nat × Nat) := [(9169711104,115801337305006,115801726802971)]
theorem point_links_checked69929 : (cuts69929.take 1).map (fun c => (9169666049-1+2*2^10*c.k,115801276066023+c.lower,115801665563951+c.upper)) = pointBounds69929 := by
 decide +kernel
def cuts69930 : List PrefixCut := [⟨64,174596856,174596961⟩]
theorem checked69930 : checkPrefixCuts (2^48) 9169797121 10 Manual.Count131072.C069930.packed 64 cuts69930 = true := by
 decide +kernel
def cuts69931 : List PrefixCut := [⟨34,92669153,92669207⟩,
⟨64,174717145,174717244⟩]
theorem checked69931 : checkPrefixCuts (2^48) 9169928193 10 Manual.Count131072.C069931.packed 64 cuts69931 = true := by
 decide +kernel
def pointBounds69931 : List (Nat × Nat × Nat) := [(9169997824,115801715782669,115802105280860)]
theorem point_links_checked69931 : (cuts69931.take 1).map (fun c => (9169928193-1+2*2^10*c.k,115801623113516+c.lower,115802012611653+c.upper)) = pointBounds69931 := by
 decide +kernel
def cuts69932 : List PrefixCut := [⟨64,172197669,172197765⟩]
theorem checked69932 : checkPrefixCuts (2^48) 9170059265 10 Manual.Count131072.C069932.packed 64 cuts69932 = true := by
 decide +kernel
def cuts69933 : List PrefixCut := [⟨46,127657989,127658065⟩,
⟨64,176492426,176492527⟩]
theorem checked69933 : checkPrefixCuts (2^48) 9170190337 10 Manual.Count131072.C069933.packed 64 cuts69933 = true := by
 decide +kernel
def pointBounds69933 : List (Nat × Nat × Nat) := [(9170284544,115802097686319,115802487184727)]
theorem point_links_checked69933 : (cuts69933.take 1).map (fun c => (9170190337-1+2*2^10*c.k,115801970028330+c.lower,115802359526662+c.upper)) = pointBounds69933 := by
 decide +kernel
def cuts69934 : List PrefixCut := [⟨64,176121574,176121673⟩]
theorem checked69934 : checkPrefixCuts (2^48) 9170321409 10 Manual.Count131072.C069934.packed 64 cuts69934 = true := by
 decide +kernel
def cuts69935 : List PrefixCut := [⟨58,158501117,158501212⟩,
⟨64,175044783,175044889⟩]
theorem checked69935 : checkPrefixCuts (2^48) 9170452481 10 Manual.Count131072.C069935.packed 64 cuts69935 = true := by
 decide +kernel
def pointBounds69935 : List (Nat × Nat × Nat) := [(9170571264,115802481143447,115802870642074)]
theorem point_links_checked69935 : (cuts69935.take 1).map (fun c => (9170452481-1+2*2^10*c.k,115802322642330+c.lower,115802712140862+c.upper)) = pointBounds69935 := by
 decide +kernel
def cuts69936 : List PrefixCut := [⟨64,175257129,175257236⟩]
theorem checked69936 : checkPrefixCuts (2^48) 9170583553 10 Manual.Count131072.C069936.packed 64 cuts69936 = true := by
 decide +kernel
def cuts69937 : List PrefixCut := [⟨64,176727864,176727973⟩]
theorem checked69937 : checkPrefixCuts (2^48) 9170714625 10 Manual.Count131072.C069937.packed 64 cuts69937 = true := by
 decide +kernel
def cuts69938 : List PrefixCut := [⟨6,15898631,15898642⟩,
⟨64,175988733,175988835⟩]
theorem checked69938 : checkPrefixCuts (2^48) 9170845697 10 Manual.Count131072.C069938.packed 64 cuts69938 = true := by
 decide +kernel
def pointBounds69938 : List (Nat × Nat × Nat) := [(9170857984,115802865570737,115803255069602)]
theorem point_links_checked69938 : (cuts69938.take 1).map (fun c => (9170845697-1+2*2^10*c.k,115802849672106+c.lower,115803239170960+c.upper)) = pointBounds69938 := by
 decide +kernel
def cuts69939 : List PrefixCut := [⟨64,176569363,176569465⟩]
theorem checked69939 : checkPrefixCuts (2^48) 9170976769 10 Manual.Count131072.C069939.packed 64 cuts69939 = true := by
 decide +kernel
def cuts69940 : List PrefixCut := [⟨18,49750794,49750821⟩,
⟨64,175646099,175646198⟩]
theorem checked69940 : checkPrefixCuts (2^48) 9171107841 10 Manual.Count131072.C069940.packed 64 cuts69940 = true := by
 decide +kernel
def pointBounds69940 : List (Nat × Nat × Nat) := [(9171144704,115803251980996,115803641480081)]
theorem point_links_checked69940 : (cuts69940.take 1).map (fun c => (9171107841-1+2*2^10*c.k,115803202230202+c.lower,115803591729260+c.upper)) = pointBounds69940 := by
 decide +kernel
def cuts69941 : List PrefixCut := [⟨64,175490121,175490231⟩]
theorem checked69941 : checkPrefixCuts (2^48) 9171238913 10 Manual.Count131072.C069941.packed 64 cuts69941 = true := by
 decide +kernel
def cuts69942 : List PrefixCut := [⟨30,81820884,81820930⟩,
⟨64,172019625,172019726⟩]
theorem checked69942 : checkPrefixCuts (2^48) 9171369985 10 Manual.Count131072.C069942.packed 64 cuts69942 = true := by
 decide +kernel
def pointBounds69942 : List (Nat × Nat × Nat) := [(9171431424,115803635187306,115804024686619)]
theorem point_links_checked69942 : (cuts69942.take 1).map (fun c => (9171369985-1+2*2^10*c.k,115803553366422+c.lower,115803942865689+c.upper)) = pointBounds69942 := by
 decide +kernel
def cuts69943 : List PrefixCut := [⟨64,176221669,176221771⟩]
theorem checked69943 : checkPrefixCuts (2^48) 9171501057 10 Manual.Count131072.C069943.packed 64 cuts69943 = true := by
 decide +kernel
def cuts69944 : List PrefixCut := [⟨42,115822489,115822554⟩,
⟨64,175758817,175758916⟩]
theorem checked69944 : checkPrefixCuts (2^48) 9171632129 10 Manual.Count131072.C069944.packed 64 cuts69944 = true := by
 decide +kernel
def pointBounds69944 : List (Nat × Nat × Nat) := [(9171718144,115804017430205,115804406929740)]
theorem point_links_checked69944 : (cuts69944.take 1).map (fun c => (9171632129-1+2*2^10*c.k,115803901607716+c.lower,115804291107186+c.upper)) = pointBounds69944 := by
 decide +kernel
def cuts69945 : List PrefixCut := [⟨64,172871531,172871629⟩]
theorem checked69945 : checkPrefixCuts (2^48) 9171763201 10 Manual.Count131072.C069945.packed 64 cuts69945 = true := by
 decide +kernel
def cuts69946 : List PrefixCut := [⟨54,146538376,146538466⟩,
⟨64,174219354,174219461⟩]
theorem checked69946 : checkPrefixCuts (2^48) 9171894273 10 Manual.Count131072.C069946.packed 64 cuts69946 = true := by
 decide +kernel
def pointBounds69946 : List (Nat × Nat × Nat) := [(9172004864,115804396776440,115804786276197)]
theorem point_links_checked69946 : (cuts69946.take 1).map (fun c => (9171894273-1+2*2^10*c.k,115804250238064+c.lower,115804639737731+c.upper)) = pointBounds69946 := by
 decide +kernel
def cuts69947 : List PrefixCut := [⟨64,178237020,178237127⟩]
theorem checked69947 : checkPrefixCuts (2^48) 9172025345 10 Manual.Count131072.C069947.packed 64 cuts69947 = true := by
 decide +kernel
def cuts69948 : List PrefixCut := [⟨64,175196393,175196492⟩]
theorem checked69948 : checkPrefixCuts (2^48) 9172156417 10 Manual.Count131072.C069948.packed 64 cuts69948 = true := by
 decide +kernel
def cuts69949 : List PrefixCut := [⟨2,5401005,5401008⟩,
⟨64,172616140,172616243⟩]
theorem checked69949 : checkPrefixCuts (2^48) 9172287489 10 Manual.Count131072.C069949.packed 64 cuts69949 = true := by
 decide +kernel
def pointBounds69949 : List (Nat × Nat × Nat) := [(9172291584,115804783291836,115805172791819)]
theorem point_links_checked69949 : (cuts69949.take 1).map (fun c => (9172287489-1+2*2^10*c.k,115804777890831+c.lower,115805167390811+c.upper)) = pointBounds69949 := by
 decide +kernel
def cuts69950 : List PrefixCut := [⟨64,175743748,175743851⟩]
theorem checked69950 : checkPrefixCuts (2^48) 9172418561 10 Manual.Count131072.C069950.packed 64 cuts69950 = true := by
 decide +kernel
def cuts69951 : List PrefixCut := [⟨14,37529724,37529748⟩,
⟨64,174084177,174084272⟩]
theorem checked69951 : checkPrefixCuts (2^48) 9172549633 10 Manual.Count131072.C069951.packed 64 cuts69951 = true := by
 decide +kernel
def pointBounds69951 : List (Nat × Nat × Nat) := [(9172578304,115805163780443,115805553280653)]
theorem point_links_checked69951 : (cuts69951.take 1).map (fun c => (9172549633-1+2*2^10*c.k,115805126250719+c.lower,115805515750905+c.upper)) = pointBounds69951 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000310
