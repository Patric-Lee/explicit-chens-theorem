import PlattAssemblyKernel
import PlattCertificates.Count131072.C020928
import PlattCertificates.Count131072.C020929
import PlattCertificates.Count131072.C020930
import PlattCertificates.Count131072.C020931
import PlattCertificates.Count131072.C020932
import PlattCertificates.Count131072.C020933
import PlattCertificates.Count131072.C020934
import PlattCertificates.Count131072.C020935
import PlattCertificates.Count131072.C020936
import PlattCertificates.Count131072.C020937
import PlattCertificates.Count131072.C020938
import PlattCertificates.Count131072.C020939
import PlattCertificates.Count131072.C020940
import PlattCertificates.Count131072.C020941
import PlattCertificates.Count131072.C020942
import PlattCertificates.Count131072.C020943
import PlattCertificates.Count131072.C020944
import PlattCertificates.Count131072.C020945
import PlattCertificates.Count131072.C020946
import PlattCertificates.Count131072.C020947
import PlattCertificates.Count131072.C020948
import PlattCertificates.Count131072.C020949
import PlattCertificates.Count131072.C020950
import PlattCertificates.Count131072.C020951
import PlattCertificates.Count131072.C020952
import PlattCertificates.Count131072.C020953
import PlattCertificates.Count131072.C020954
import PlattCertificates.Count131072.C020955
import PlattCertificates.Count131072.C020956
import PlattCertificates.Count131072.C020957
import PlattCertificates.Count131072.C020958
import PlattCertificates.Count131072.C020959
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000029
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts20928 : List PrefixCut := [⟨61,288643484,288643657⟩,
⟨128,610785346,610785704⟩]
theorem checked20928 : checkPrefixCuts (2^48) 2747006977 9 Manual.Count131072.C020928.packed 128 cuts20928 = true := by
 decide +kernel
def pointBounds20928 : List (Nat × Nat × Nat) := [(2747069440,100608209559431,100608590272089)]
theorem point_links_checked20928 : (cuts20928.take 1).map (fun c => (2747006977-1+2*2^9*c.k,100607920915947+c.lower,100608301628432+c.upper)) = pointBounds20928 := by
 decide +kernel
def cuts20929 : List PrefixCut := [⟨17,82788343,82788390⟩,
⟨101,484529629,484529909⟩,
⟨128,614752177,614752531⟩]
theorem checked20929 : checkPrefixCuts (2^48) 2747138049 9 Manual.Count131072.C020929.packed 128 cuts20929 = true := by
 decide +kernel
def pointBounds20929 : List (Nat × Nat × Nat) := [(2747155456,100608614489636,100608995202526),(2747241472,100609016230922,100609396944045)]
theorem point_links_checked20929 : (cuts20929.take 2).map (fun c => (2747138049-1+2*2^9*c.k,100608531701293+c.lower,100608912414136+c.upper)) = pointBounds20929 := by
 decide +kernel
def cuts20930 : List PrefixCut := [⟨57,275194574,275194737⟩,
⟨128,621689681,621690051⟩]
theorem checked20930 : checkPrefixCuts (2^48) 2747269121 9 Manual.Count131072.C020930.packed 128 cuts20930 = true := by
 decide +kernel
def pointBounds20930 : List (Nat × Nat × Nat) := [(2747327488,100609421648044,100609802361404)]
theorem point_links_checked20930 : (cuts20930.take 1).map (fun c => (2747269121-1+2*2^9*c.k,100609146453470+c.lower,100609527166667+c.upper)) = pointBounds20930 := by
 decide +kernel
def cuts20931 : List PrefixCut := [⟨13,60446157,60446191⟩,
⟨97,458871382,458871648⟩,
⟨128,608341662,608342015⟩]
theorem checked20931 : checkPrefixCuts (2^48) 2747400193 9 Manual.Count131072.C020931.packed 128 cuts20931 = true := by
 decide +kernel
def pointBounds20931 : List (Nat × Nat × Nat) := [(2747413504,100609828589308,100610209302909),(2747499520,100610227014533,100610607728366)]
theorem point_links_checked20931 : (cuts20931.take 2).map (fun c => (2747400193-1+2*2^9*c.k,100609768143151+c.lower,100610148856718+c.upper)) = pointBounds20931 := by
 decide +kernel
def cuts20932 : List PrefixCut := [⟨53,255806308,255806459⟩,
⟨128,622552367,622552728⟩]
theorem checked20932 : checkPrefixCuts (2^48) 2747531265 9 Manual.Count131072.C020932.packed 128 cuts20932 = true := by
 decide +kernel
def pointBounds20932 : List (Nat × Nat × Nat) := [(2747585536,100610632291121,100611013005192)]
theorem point_links_checked20932 : (cuts20932.take 1).map (fun c => (2747531265-1+2*2^9*c.k,100610376484813+c.lower,100610757198733+c.upper)) = pointBounds20932 := by
 decide +kernel
def cuts20933 : List PrefixCut := [⟨9,41488773,41488798⟩,
⟨93,445305849,445306108⟩,
⟨128,617707959,617708317⟩]
theorem checked20933 : checkPrefixCuts (2^48) 2747662337 9 Manual.Count131072.C020933.packed 128 cuts20933 = true := by
 decide +kernel
def pointBounds20933 : List (Nat × Nat × Nat) := [(2747671552,100611040525953,100611421240259),(2747757568,100611444343029,100611825057569)]
theorem point_links_checked20933 : (cuts20933.take 2).map (fun c => (2747662337-1+2*2^9*c.k,100610999037180+c.lower,100611379751461+c.upper)) = pointBounds20933 := by
 decide +kernel
def cuts20934 : List PrefixCut := [⟨49,238060711,238060844⟩,
⟨128,608049860,608050211⟩]
theorem checked20934 : checkPrefixCuts (2^48) 2747793409 9 Manual.Count131072.C020934.packed 128 cuts20934 = true := by
 decide +kernel
def pointBounds20934 : List (Nat × Nat × Nat) := [(2747843584,100611854805850,100612235520622)]
theorem point_links_checked20934 : (cuts20934.take 1).map (fun c => (2747793409-1+2*2^9*c.k,100611616745139+c.lower,100611997459778+c.upper)) = pointBounds20934 := by
 decide +kernel
def cuts20935 : List PrefixCut := [⟨5,25095771,25095786⟩,
⟨89,435532812,435533068⟩,
⟨128,621951182,621951547⟩]
theorem checked20935 : checkPrefixCuts (2^48) 2747924481 9 Manual.Count131072.C020935.packed 128 cuts20935 = true := by
 decide +kernel
def pointBounds20935 : List (Nat × Nat × Nat) := [(2747929600,100612249890770,100612630605775),(2748015616,100612660327811,100613041043057)]
theorem point_links_checked20935 : (cuts20935.take 2).map (fun c => (2747924481-1+2*2^9*c.k,100612224794999+c.lower,100612605509989+c.upper)) = pointBounds20935 := by
 decide +kernel
def cuts20936 : List PrefixCut := [⟨45,215606897,215607025⟩,
⟨128,617517234,617517588⟩]
theorem checked20936 : checkPrefixCuts (2^48) 2748055553 9 Manual.Count131072.C020936.packed 128 cuts20936 = true := by
 decide +kernel
def pointBounds20936 : List (Nat × Nat × Nat) := [(2748101632,100613062353078,100613443068561)]
theorem point_links_checked20936 : (cuts20936.take 1).map (fun c => (2748055553-1+2*2^9*c.k,100612846746181+c.lower,100613227461536+c.upper)) = pointBounds20936 := by
 decide +kernel
def cuts20937 : List PrefixCut := [⟨1,4916257,4916260⟩,
⟨85,403741283,403741519⟩,
⟨128,610830451,610830811⟩]
theorem checked20937 : checkPrefixCuts (2^48) 2748186625 9 Manual.Count131072.C020937.packed 128 cuts20937 = true := by
 decide +kernel
def pointBounds20937 : List (Nat × Nat × Nat) := [(2748187648,100613469179672,100613849895384),(2748273664,100613868004698,100614248720643)]
theorem point_links_checked20937 : (cuts20937.take 2).map (fun c => (2748186625-1+2*2^9*c.k,100613464263415+c.lower,100613844979124+c.upper)) = pointBounds20937 := by
 decide +kernel
def cuts20938 : List PrefixCut := [⟨41,195717722,195717839⟩,
⟨125,601686792,601687139⟩,
⟨128,617560704,617561060⟩]
theorem checked20938 : checkPrefixCuts (2^48) 2748317697 9 Manual.Count131072.C020938.packed 128 cuts20938 = true := by
 decide +kernel
def pointBounds20938 : List (Nat × Nat × Nat) := [(2748359680,100614270811588,100614651527774),(2748445696,100614676780658,100615057497074)]
theorem point_links_checked20938 : (cuts20938.take 2).map (fun c => (2748317697-1+2*2^9*c.k,100614075093866+c.lower,100614455809935+c.upper)) = pointBounds20938 := by
 decide +kernel
def cuts20939 : List PrefixCut := [⟨81,383835417,383835643⟩,
⟨128,607187879,607188237⟩]
theorem checked20939 : checkPrefixCuts (2^48) 2748448769 9 Manual.Count131072.C020939.packed 128 cuts20939 = true := by
 decide +kernel
def pointBounds20939 : List (Nat × Nat × Nat) := [(2748531712,100615076489987,100615457206638)]
theorem point_links_checked20939 : (cuts20939.take 1).map (fun c => (2748448769-1+2*2^9*c.k,100614692654570+c.lower,100615073370995+c.upper)) = pointBounds20939 := by
 decide +kernel
def cuts20940 : List PrefixCut := [⟨37,179826133,179826238⟩,
⟨121,585245069,585245406⟩,
⟨128,618423523,618423881⟩]
theorem checked20940 : checkPrefixCuts (2^48) 2748579841 9 Manual.Count131072.C020940.packed 128 cuts20940 = true := by
 decide +kernel
def pointBounds20940 : List (Nat × Nat × Nat) := [(2748617728,100615479668582,100615860385470),(2748703744,100615885087518,100616265804638)]
theorem point_links_checked20940 : (cuts20940.take 2).map (fun c => (2748579841-1+2*2^9*c.k,100615299842449+c.lower,100615680559232+c.upper)) = pointBounds20940 := by
 decide +kernel
def cuts20941 : List PrefixCut := [⟨77,374583024,374583243⟩,
⟨128,627302804,627303166⟩]
theorem checked20941 : checkPrefixCuts (2^48) 2748710913 9 Manual.Count131072.C020941.packed 128 cuts20941 = true := by
 decide +kernel
def pointBounds20941 : List (Nat × Nat × Nat) := [(2748789760,100616292848996,100616673566356)]
theorem point_links_checked20941 : (cuts20941.take 1).map (fun c => (2748710913-1+2*2^9*c.k,100615918265972+c.lower,100616298983113+c.upper)) = pointBounds20941 := by
 decide +kernel
def cuts20942 : List PrefixCut := [⟨33,159534523,159534613⟩,
⟨117,569523085,569523409⟩,
⟨128,622050670,622051025⟩]
theorem checked20942 : checkPrefixCuts (2^48) 2748841985 9 Manual.Count131072.C020942.packed 128 cuts20942 = true := by
 decide +kernel
def pointBounds20942 : List (Nat × Nat × Nat) := [(2748875776,100616705103299,100617085820892),(2748961792,100617115091861,100617495809688)]
theorem point_links_checked20942 : (cuts20942.take 2).map (fun c => (2748841985-1+2*2^9*c.k,100616545568776+c.lower,100616926286279+c.upper)) = pointBounds20942 := by
 decide +kernel
def cuts20943 : List PrefixCut := [⟨73,356117101,356117307⟩,
⟨128,621713928,621714288⟩]
theorem checked20943 : checkPrefixCuts (2^48) 2748973057 9 Manual.Count131072.C020943.packed 128 cuts20943 = true := by
 decide +kernel
def pointBounds20943 : List (Nat × Nat × Nat) := [(2749047808,100617523736547,100617904454611)]
theorem point_links_checked20943 : (cuts20943.take 1).map (fun c => (2748973057-1+2*2^9*c.k,100617167619446+c.lower,100617548337304+c.upper)) = pointBounds20943 := by
 decide +kernel
def cuts20944 : List PrefixCut := [⟨29,136379883,136379963⟩,
⟨113,535272572,535272883⟩,
⟨128,605712257,605712609⟩]
theorem checked20944 : checkPrefixCuts (2^48) 2749104129 9 Manual.Count131072.C020944.packed 128 cuts20944 = true := by
 decide +kernel
def pointBounds20944 : List (Nat × Nat × Nat) := [(2749133824,100617925713257,100618306431555),(2749219840,100618324605946,100618705324475)]
theorem point_links_checked20944 : (cuts20944.take 2).map (fun c => (2749104129-1+2*2^9*c.k,100617789333374+c.lower,100618170051592+c.upper)) = pointBounds20944 := by
 decide +kernel
def cuts20945 : List PrefixCut := [⟨69,335095184,335095383⟩,
⟨128,626773576,626773944⟩]
theorem checked20945 : checkPrefixCuts (2^48) 2749235201 9 Manual.Count131072.C020945.packed 128 cuts20945 = true := by
 decide +kernel
def pointBounds20945 : List (Nat × Nat × Nat) := [(2749305856,100618730140815,100619110859584)]
theorem point_links_checked20945 : (cuts20945.take 1).map (fun c => (2749235201-1+2*2^9*c.k,100618395045631+c.lower,100618775764201+c.upper)) = pointBounds20945 := by
 decide +kernel
def cuts20946 : List PrefixCut := [⟨25,117939011,117939080⟩,
⟨109,524267606,524267913⟩,
⟨128,616608582,616608939⟩]
theorem checked20946 : checkPrefixCuts (2^48) 2749366273 9 Manual.Count131072.C020946.packed 128 cuts20946 = true := by
 decide +kernel
def pointBounds20946 : List (Nat × Nat × Nat) := [(2749391872,100619139758218,100619520477225),(2749477888,100619546086813,100619926806058)]
theorem point_links_checked20946 : (cuts20946.take 2).map (fun c => (2749366273-1+2*2^9*c.k,100619021819207+c.lower,100619402538145+c.upper)) = pointBounds20946 := by
 decide +kernel
def cuts20947 : List PrefixCut := [⟨65,312234525,312234705⟩,
⟨128,614736532,614736888⟩]
theorem checked20947 : checkPrefixCuts (2^48) 2749497345 9 Manual.Count131072.C020947.packed 128 cuts20947 = true := by
 decide +kernel
def pointBounds20947 : List (Nat × Nat × Nat) := [(2749563904,100619950662314,100620331381789)]
theorem point_links_checked20947 : (cuts20947.take 1).map (fun c => (2749497345-1+2*2^9*c.k,100619638427789+c.lower,100620019147084+c.upper)) = pointBounds20947 := by
 decide +kernel
def cuts20948 : List PrefixCut := [⟨21,100525309,100525370⟩,
⟨105,510705566,510705859⟩,
⟨128,621565672,621566030⟩]
theorem checked20948 : checkPrefixCuts (2^48) 2749628417 9 Manual.Count131072.C020948.packed 128 cuts20948 = true := by
 decide +kernel
def pointBounds20948 : List (Nat × Nat × Nat) := [(2749649920,100620353689630,100620734409342),(2749735936,100620763869887,100621144589831)]
theorem point_links_checked20948 : (cuts20948.take 2).map (fun c => (2749628417-1+2*2^9*c.k,100620253164321+c.lower,100620633883972+c.upper)) = pointBounds20948 := by
 decide +kernel
def cuts20949 : List PrefixCut := [⟨61,293472707,293472881⟩,
⟨128,609867035,609867391⟩]
theorem checked20949 : checkPrefixCuts (2^48) 2749759489 9 Manual.Count131072.C020949.packed 128 cuts20949 = true := by
 decide +kernel
def pointBounds20949 : List (Nat × Nat × Nat) := [(2749821952,100621168202700,100621548922883)]
theorem point_links_checked20949 : (cuts20949.take 1).map (fun c => (2749759489-1+2*2^9*c.k,100620874729993+c.lower,100621255450002+c.upper)) = pointBounds20949 := by
 decide +kernel
def cuts20950 : List PrefixCut := [⟨17,81067740,81067786⟩,
⟨101,483635215,483635493⟩,
⟨128,612703870,612704225⟩]
theorem checked20950 : checkPrefixCuts (2^48) 2749890561 9 Manual.Count131072.C020950.packed 128 cuts20950 = true := by
 decide +kernel
def pointBounds20950 : List (Nat × Nat × Nat) := [(2749907968,100621565664768,100621946385179),(2749993984,100621968232243,100622348952886)]
theorem point_links_checked20950 : (cuts20950.take 2).map (fun c => (2749890561-1+2*2^9*c.k,100621484597028+c.lower,100621865317393+c.upper)) = pointBounds20950 := by
 decide +kernel
def cuts20951 : List PrefixCut := [⟨57,272667372,272667529⟩,
⟨128,610218242,610218598⟩]
theorem checked20951 : checkPrefixCuts (2^48) 2750021633 9 Manual.Count131072.C020951.packed 128 cuts20951 = true := by
 decide +kernel
def pointBounds20951 : List (Nat × Nat × Nat) := [(2750080000,100622369968270,100622750689147)]
theorem point_links_checked20951 : (cuts20951.take 1).map (fun c => (2750021633-1+2*2^9*c.k,100622097300898+c.lower,100622478021618+c.upper)) = pointBounds20951 := by
 decide +kernel
def cuts20952 : List PrefixCut := [⟨13,62637331,62637367⟩,
⟨97,463631832,463632103⟩,
⟨128,616227523,616227883⟩]
theorem checked20952 : checkPrefixCuts (2^48) 2750152705 9 Manual.Count131072.C020952.packed 128 cuts20952 = true := by
 decide +kernel
def pointBounds20952 : List (Nat × Nat × Nat) := [(2750166016,100622770156471,100623150877583),(2750252032,100623171150972,100623551872319)]
theorem point_links_checked20952 : (cuts20952.take 2).map (fun c => (2750152705-1+2*2^9*c.k,100622707519140+c.lower,100623088240216+c.upper)) = pointBounds20952 := by
 decide +kernel
def cuts20953 : List PrefixCut := [⟨53,258006541,258006690⟩,
⟨128,615891271,615891632⟩]
theorem checked20953 : checkPrefixCuts (2^48) 2750283777 9 Manual.Count131072.C020953.packed 128 cuts20953 = true := by
 decide +kernel
def pointBounds20953 : List (Nat × Nat × Nat) := [(2750338048,100623581753204,100623962474789)]
theorem point_links_checked20953 : (cuts20953.take 1).map (fun c => (2750283777-1+2*2^9*c.k,100623323746663+c.lower,100623704468099+c.upper)) = pointBounds20953 := by
 decide +kernel
def cuts20954 : List PrefixCut := [⟨9,44108065,44108090⟩,
⟨93,448953709,448953968⟩,
⟨128,624048657,624049014⟩]
theorem checked20954 : checkPrefixCuts (2^48) 2750414849 9 Manual.Count131072.C020954.packed 128 cuts20954 = true := by
 decide +kernel
def pointBounds20954 : List (Nat × Nat × Nat) := [(2750424064,100623983745999,100624364467821),(2750510080,100624388591643,100624769313699)]
theorem point_links_checked20954 : (cuts20954.take 2).map (fun c => (2750414849-1+2*2^9*c.k,100623939637934+c.lower,100624320359731+c.upper)) = pointBounds20954 := by
 decide +kernel
def cuts20955 : List PrefixCut := [⟨49,237310813,237310950⟩,
⟨128,616753497,616753857⟩]
theorem checked20955 : checkPrefixCuts (2^48) 2750545921 9 Manual.Count131072.C020955.packed 128 cuts20955 = true := by
 decide +kernel
def pointBounds20955 : List (Nat × Nat × Nat) := [(2750596096,100624800997404,100625181719695)]
theorem point_links_checked20955 : (cuts20955.take 1).map (fun c => (2750545921-1+2*2^9*c.k,100624563686591+c.lower,100624944408745+c.upper)) = pointBounds20955 := by
 decide +kernel
def cuts20956 : List PrefixCut := [⟨5,26810256,26810271⟩,
⟨89,434585450,434585705⟩,
⟨128,622352152,622352516⟩]
theorem checked20956 : checkPrefixCuts (2^48) 2750676993 9 Manual.Count131072.C020956.packed 128 cuts20956 = true := by
 decide +kernel
def pointBounds20956 : List (Nat × Nat × Nat) := [(2750682112,100625207250344,100625587972873),(2750768128,100625615025538,100625995748307)]
theorem point_links_checked20956 : (cuts20956.take 2).map (fun c => (2750676993-1+2*2^9*c.k,100625180440088+c.lower,100625561162602+c.upper)) = pointBounds20956 := by
 decide +kernel
def cuts20957 : List PrefixCut := [⟨45,215800426,215800552⟩,
⟨128,614034328,614034685⟩]
theorem checked20957 : checkPrefixCuts (2^48) 2750808065 9 Manual.Count131072.C020957.packed 128 cuts20957 = true := by
 decide +kernel
def pointBounds20957 : List (Nat × Nat × Nat) := [(2750854144,100626018592666,100626399315670)]
theorem point_links_checked20957 : (cuts20957.take 1).map (fun c => (2750808065-1+2*2^9*c.k,100625802792240+c.lower,100626183515118+c.upper)) = pointBounds20957 := by
 decide +kernel
def cuts20958 : List PrefixCut := [⟨1,4502060,4502063⟩,
⟨85,409988007,409988245⟩,
⟨128,621576462,621576813⟩]
theorem checked20958 : checkPrefixCuts (2^48) 2750939137 9 Manual.Count131072.C020958.packed 128 cuts20958 = true := by
 decide +kernel
def pointBounds20958 : List (Nat × Nat × Nat) := [(2750940160,100626421328628,100626802051866),(2751026176,100626826814575,100627207538048)]
theorem point_links_checked20958 : (cuts20958.take 2).map (fun c => (2750939137-1+2*2^9*c.k,100626416826568+c.lower,100626797549803+c.upper)) = pointBounds20958 := by
 decide +kernel
def cuts20959 : List PrefixCut := [⟨41,197772791,197772904⟩,
⟨125,609576735,609577090⟩,
⟨128,624104737,624105101⟩]
theorem checked20959 : checkPrefixCuts (2^48) 2751070209 9 Manual.Count131072.C020959.packed 128 cuts20959 = true := by
 decide +kernel
def pointBounds20959 : List (Nat × Nat × Nat) := [(2751112192,100627236175821,100627616899520),(2751198208,100627647979765,100628028703706)]
theorem point_links_checked20959 : (cuts20959.take 2).map (fun c => (2751070209-1+2*2^9*c.k,100627038403030+c.lower,100627419126616+c.upper)) = pointBounds20959 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000029
