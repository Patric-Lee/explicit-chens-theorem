import PlattAssemblyKernel
import PlattCertificates.Count131072.C068928
import PlattCertificates.Count131072.C068929
import PlattCertificates.Count131072.C068930
import PlattCertificates.Count131072.C068931
import PlattCertificates.Count131072.C068932
import PlattCertificates.Count131072.C068933
import PlattCertificates.Count131072.C068934
import PlattCertificates.Count131072.C068935
import PlattCertificates.Count131072.C068936
import PlattCertificates.Count131072.C068937
import PlattCertificates.Count131072.C068938
import PlattCertificates.Count131072.C068939
import PlattCertificates.Count131072.C068940
import PlattCertificates.Count131072.C068941
import PlattCertificates.Count131072.C068942
import PlattCertificates.Count131072.C068943
import PlattCertificates.Count131072.C068944
import PlattCertificates.Count131072.C068945
import PlattCertificates.Count131072.C068946
import PlattCertificates.Count131072.C068947
import PlattCertificates.Count131072.C068948
import PlattCertificates.Count131072.C068949
import PlattCertificates.Count131072.C068950
import PlattCertificates.Count131072.C068951
import PlattCertificates.Count131072.C068952
import PlattCertificates.Count131072.C068953
import PlattCertificates.Count131072.C068954
import PlattCertificates.Count131072.C068955
import PlattCertificates.Count131072.C068956
import PlattCertificates.Count131072.C068957
import PlattCertificates.Count131072.C068958
import PlattCertificates.Count131072.C068959
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000279
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts68928 : List PrefixCut := [⟨64,179656300,179656401⟩]
theorem checked68928 : checkPrefixCuts (2^48) 9038462977 10 Manual.Count131072.C068928.packed 64 cuts68928 = true := by
 decide +kernel
def cuts68929 : List PrefixCut := [⟨31,86541770,86541817⟩,
⟨64,178190064,178190159⟩]
theorem checked68929 : checkPrefixCuts (2^48) 9038594049 10 Manual.Count131072.C068929.packed 64 cuts68929 = true := by
 decide +kernel
def pointBounds68929 : List (Nat × Nat × Nat) := [(9038657536,115624686635478,115625076029501)]
theorem point_links_checked68929 : (cuts68929.take 1).map (fun c => (9038594049-1+2*2^10*c.k,115624600093708+c.lower,115624989487684+c.upper)) = pointBounds68929 := by
 decide +kernel
def cuts68930 : List PrefixCut := [⟨64,178561174,178561278⟩]
theorem checked68930 : checkPrefixCuts (2^48) 9038725121 10 Manual.Count131072.C068930.packed 64 cuts68930 = true := by
 decide +kernel
def cuts68931 : List PrefixCut := [⟨41,115219474,115219539⟩,
⟨64,178838851,178838953⟩]
theorem checked68931 : checkPrefixCuts (2^48) 9038856193 10 Manual.Count131072.C068931.packed 64 cuts68931 = true := by
 decide +kernel
def pointBounds68931 : List (Nat × Nat × Nat) := [(9038940160,115625072064420,115625461458660)]
theorem point_links_checked68931 : (cuts68931.take 1).map (fun c => (9038856193-1+2*2^10*c.k,115624956844946+c.lower,115625346239121+c.upper)) = pointBounds68931 := by
 decide +kernel
def cuts68932 : List PrefixCut := [⟨64,179054237,179054343⟩]
theorem checked68932 : checkPrefixCuts (2^48) 9038987265 10 Manual.Count131072.C068932.packed 64 cuts68932 = true := by
 decide +kernel
def cuts68933 : List PrefixCut := [⟨51,141186311,141186392⟩,
⟨64,177183265,177183368⟩]
theorem checked68933 : checkPrefixCuts (2^48) 9039118337 10 Manual.Count131072.C068933.packed 64 cuts68933 = true := by
 decide +kernel
def pointBounds68933 : List (Nat × Nat × Nat) := [(9039222784,115625455924345,115625845318809)]
theorem point_links_checked68933 : (cuts68933.take 1).map (fun c => (9039118337-1+2*2^10*c.k,115625314738034+c.lower,115625704132417+c.upper)) = pointBounds68933 := by
 decide +kernel
def cuts68934 : List PrefixCut := [⟨64,179049034,179049137⟩]
theorem checked68934 : checkPrefixCuts (2^48) 9039249409 10 Manual.Count131072.C068934.packed 64 cuts68934 = true := by
 decide +kernel
def cuts68935 : List PrefixCut := [⟨61,167525251,167525348⟩,
⟨64,175839176,175839278⟩]
theorem checked68935 : checkPrefixCuts (2^48) 9039380481 10 Manual.Count131072.C068935.packed 64 cuts68935 = true := by
 decide +kernel
def pointBounds68935 : List (Nat × Nat × Nat) := [(9039505408,115625838495584,115626227890270)]
theorem point_links_checked68935 : (cuts68935.take 1).map (fun c => (9039380481-1+2*2^10*c.k,115625670970333+c.lower,115626060364922+c.upper)) = pointBounds68935 := by
 decide +kernel
def cuts68936 : List PrefixCut := [⟨64,178265390,178265497⟩]
theorem checked68936 : checkPrefixCuts (2^48) 9039511553 10 Manual.Count131072.C068936.packed 64 cuts68936 = true := by
 decide +kernel
def cuts68937 : List PrefixCut := [⟨64,179881960,179882063⟩]
theorem checked68937 : checkPrefixCuts (2^48) 9039642625 10 Manual.Count131072.C068937.packed 64 cuts68937 = true := by
 decide +kernel
def cuts68938 : List PrefixCut := [⟨7,20488383,20488395⟩,
⟨64,177544076,177544182⟩]
theorem checked68938 : checkPrefixCuts (2^48) 9039773697 10 Manual.Count131072.C068938.packed 64 cuts68938 = true := by
 decide +kernel
def pointBounds68938 : List (Nat × Nat × Nat) := [(9039788032,115626225445242,115626614840155)]
theorem point_links_checked68938 : (cuts68938.take 1).map (fun c => (9039773697-1+2*2^10*c.k,115626204956859+c.lower,115626594351760+c.upper)) = pointBounds68938 := by
 decide +kernel
def cuts68939 : List PrefixCut := [⟨64,179845599,179845707⟩]
theorem checked68939 : checkPrefixCuts (2^48) 9039904769 10 Manual.Count131072.C068939.packed 64 cuts68939 = true := by
 decide +kernel
def cuts68940 : List PrefixCut := [⟨17,48168042,48168069⟩,
⟨64,176916205,176916312⟩]
theorem checked68940 : checkPrefixCuts (2^48) 9040035841 10 Manual.Count131072.C068940.packed 64 cuts68940 = true := by
 decide +kernel
def pointBounds68940 : List (Nat × Nat × Nat) := [(9040070656,115626610514576,115626999909718)]
theorem point_links_checked68940 : (cuts68940.take 1).map (fun c => (9040035841-1+2*2^10*c.k,115626562346534+c.lower,115626951741649+c.upper)) = pointBounds68940 := by
 decide +kernel
def cuts68941 : List PrefixCut := [⟨64,179186543,179186646⟩]
theorem checked68941 : checkPrefixCuts (2^48) 9040166913 10 Manual.Count131072.C068941.packed 64 cuts68941 = true := by
 decide +kernel
def cuts68942 : List PrefixCut := [⟨27,73666551,73666596⟩,
⟨64,178031930,178032037⟩]
theorem checked68942 : checkPrefixCuts (2^48) 9040297985 10 Manual.Count131072.C068942.packed 64 cuts68942 = true := by
 decide +kernel
def pointBounds68942 : List (Nat × Nat × Nat) := [(9040353280,115626992115833,115627381511203)]
theorem point_links_checked68942 : (cuts68942.take 1).map (fun c => (9040297985-1+2*2^10*c.k,115626918449282+c.lower,115627307844607+c.upper)) = pointBounds68942 := by
 decide +kernel
def cuts68943 : List PrefixCut := [⟨64,176410339,176410448⟩]
theorem checked68943 : checkPrefixCuts (2^48) 9040429057 10 Manual.Count131072.C068943.packed 64 cuts68943 = true := by
 decide +kernel
def cuts68944 : List PrefixCut := [⟨37,104113918,104113977⟩,
⟨64,179178754,179178860⟩]
theorem checked68944 : checkPrefixCuts (2^48) 9040560129 10 Manual.Count131072.C068944.packed 64 cuts68944 = true := by
 decide +kernel
def pointBounds68944 : List (Nat × Nat × Nat) := [(9040635904,115627377005469,115627766401069)]
theorem point_links_checked68944 : (cuts68944.take 1).map (fun c => (9040560129-1+2*2^10*c.k,115627272891551+c.lower,115627662287092+c.upper)) = pointBounds68944 := by
 decide +kernel
def cuts68945 : List PrefixCut := [⟨64,177308096,177308196⟩]
theorem checked68945 : checkPrefixCuts (2^48) 9040691201 10 Manual.Count131072.C068945.packed 64 cuts68945 = true := by
 decide +kernel
def cuts68946 : List PrefixCut := [⟨47,127710059,127710132⟩,
⟨64,175780002,175780101⟩]
theorem checked68946 : checkPrefixCuts (2^48) 9040822273 10 Manual.Count131072.C068946.packed 64 cuts68946 = true := by
 decide +kernel
def pointBounds68946 : List (Nat × Nat × Nat) := [(9040918528,115627757088460,115628146484280)]
theorem point_links_checked68946 : (cuts68946.take 1).map (fun c => (9040822273-1+2*2^10*c.k,115627629378401+c.lower,115628018774148+c.upper)) = pointBounds68946 := by
 decide +kernel
def cuts68947 : List PrefixCut := [⟨64,178299228,178299329⟩]
theorem checked68947 : checkPrefixCuts (2^48) 9040953345 10 Manual.Count131072.C068947.packed 64 cuts68947 = true := by
 decide +kernel
def cuts68948 : List PrefixCut := [⟨57,158029421,158029516⟩,
⟨64,177954184,177954291⟩]
theorem checked68948 : checkPrefixCuts (2^48) 9041084417 10 Manual.Count131072.C068948.packed 64 cuts68948 = true := by
 decide +kernel
def pointBounds68948 : List (Nat × Nat × Nat) := [(9041201152,115628141487052,115628530883094)]
theorem point_links_checked68948 : (cuts68948.take 1).map (fun c => (9041084417-1+2*2^10*c.k,115627983457631+c.lower,115628372853578+c.upper)) = pointBounds68948 := by
 decide +kernel
def cuts68949 : List PrefixCut := [⟨64,177764825,177764928⟩]
theorem checked68949 : checkPrefixCuts (2^48) 9041215489 10 Manual.Count131072.C068949.packed 64 cuts68949 = true := by
 decide +kernel
def cuts68950 : List PrefixCut := [⟨64,177731101,177731210⟩]
theorem checked68950 : checkPrefixCuts (2^48) 9041346561 10 Manual.Count131072.C068950.packed 64 cuts68950 = true := by
 decide +kernel
def cuts68951 : List PrefixCut := [⟨3,8592295,8592300⟩,
⟨64,177635126,177635232⟩]
theorem checked68951 : checkPrefixCuts (2^48) 9041477633 10 Manual.Count131072.C068951.packed 64 cuts68951 = true := by
 decide +kernel
def pointBounds68951 : List (Nat × Nat × Nat) := [(9041483776,115628525500036,115628914896307)]
theorem point_links_checked68951 : (cuts68951.take 1).map (fun c => (9041477633-1+2*2^10*c.k,115628516907741+c.lower,115628906304007+c.upper)) = pointBounds68951 := by
 decide +kernel
def cuts68952 : List PrefixCut := [⟨64,176947687,176947779⟩]
theorem checked68952 : checkPrefixCuts (2^48) 9041608705 10 Manual.Count131072.C068952.packed 64 cuts68952 = true := by
 decide +kernel
def cuts68953 : List PrefixCut := [⟨13,35302062,35302083⟩,
⟨64,176353631,176353736⟩]
theorem checked68953 : checkPrefixCuts (2^48) 9041739777 10 Manual.Count131072.C068953.packed 64 cuts68953 = true := by
 decide +kernel
def pointBounds68953 : List (Nat × Nat × Nat) := [(9041766400,115628906792616,115629296189101)]
theorem point_links_checked68953 : (cuts68953.take 1).map (fun c => (9041739777-1+2*2^10*c.k,115628871490554+c.lower,115629260887018+c.upper)) = pointBounds68953 := by
 decide +kernel
def cuts68954 : List PrefixCut := [⟨64,178218880,178218982⟩]
theorem checked68954 : checkPrefixCuts (2^48) 9041870849 10 Manual.Count131072.C068954.packed 64 cuts68954 = true := by
 decide +kernel
def cuts68955 : List PrefixCut := [⟨23,64313813,64313852⟩,
⟨64,177967266,177967375⟩]
theorem checked68955 : checkPrefixCuts (2^48) 9042001921 10 Manual.Count131072.C068955.packed 64 cuts68955 = true := by
 decide +kernel
def pointBounds68955 : List (Nat × Nat × Nat) := [(9042049024,115629290376878,115629679773588)]
theorem point_links_checked68955 : (cuts68955.take 1).map (fun c => (9042001921-1+2*2^10*c.k,115629226063065+c.lower,115629615459736+c.upper)) = pointBounds68955 := by
 decide +kernel
def cuts68956 : List PrefixCut := [⟨64,176501608,176501715⟩]
theorem checked68956 : checkPrefixCuts (2^48) 9042132993 10 Manual.Count131072.C068956.packed 64 cuts68956 = true := by
 decide +kernel
def cuts68957 : List PrefixCut := [⟨33,90895778,90895829⟩,
⟨64,176685831,176685931⟩]
theorem checked68957 : checkPrefixCuts (2^48) 9042264065 10 Manual.Count131072.C068957.packed 64 cuts68957 = true := by
 decide +kernel
def pointBounds68957 : List (Nat × Nat × Nat) := [(9042331648,115629671427717,115630060824655)]
theorem point_links_checked68957 : (cuts68957.take 1).map (fun c => (9042264065-1+2*2^10*c.k,115629580531939+c.lower,115629969928826+c.upper)) = pointBounds68957 := by
 decide +kernel
def cuts68958 : List PrefixCut := [⟨64,179920588,179920695⟩]
theorem checked68958 : checkPrefixCuts (2^48) 9042395137 10 Manual.Count131072.C068958.packed 64 cuts68958 = true := by
 decide +kernel
def cuts68959 : List PrefixCut := [⟨43,118876890,118876955⟩,
⟨64,177801300,177801400⟩]
theorem checked68959 : checkPrefixCuts (2^48) 9042526209 10 Manual.Count131072.C068959.packed 64 cuts68959 = true := by
 decide +kernel
def pointBounds68959 : List (Nat × Nat × Nat) := [(9042614272,115630056015248,115630445412407)]
theorem point_links_checked68959 : (cuts68959.take 1).map (fun c => (9042526209-1+2*2^10*c.k,115629937138358+c.lower,115630326535452+c.upper)) = pointBounds68959 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000279
