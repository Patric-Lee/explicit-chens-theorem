import PlattAssemblyKernel
import PlattCertificates.Count131072.C067040
import PlattCertificates.Count131072.C067041
import PlattCertificates.Count131072.C067042
import PlattCertificates.Count131072.C067043
import PlattCertificates.Count131072.C067044
import PlattCertificates.Count131072.C067045
import PlattCertificates.Count131072.C067046
import PlattCertificates.Count131072.C067047
import PlattCertificates.Count131072.C067048
import PlattCertificates.Count131072.C067049
import PlattCertificates.Count131072.C067050
import PlattCertificates.Count131072.C067051
import PlattCertificates.Count131072.C067052
import PlattCertificates.Count131072.C067053
import PlattCertificates.Count131072.C067054
import PlattCertificates.Count131072.C067055
import PlattCertificates.Count131072.C067056
import PlattCertificates.Count131072.C067057
import PlattCertificates.Count131072.C067058
import PlattCertificates.Count131072.C067059
import PlattCertificates.Count131072.C067060
import PlattCertificates.Count131072.C067061
import PlattCertificates.Count131072.C067062
import PlattCertificates.Count131072.C067063
import PlattCertificates.Count131072.C067064
import PlattCertificates.Count131072.C067065
import PlattCertificates.Count131072.C067066
import PlattCertificates.Count131072.C067067
import PlattCertificates.Count131072.C067068
import PlattCertificates.Count131072.C067069
import PlattCertificates.Count131072.C067070
import PlattCertificates.Count131072.C067071
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000220
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts67040 : List PrefixCut := [⟨64,181511727,181511835⟩]
theorem checked67040 : checkPrefixCuts (2^48) 8790999041 10 Manual.Count131072.C067040.packed 64 cuts67040 = true := by
 decide +kernel
def cuts67041 : List PrefixCut := [⟨49,140014161,140014241⟩,
⟨64,183173930,183174038⟩]
theorem checked67041 : checkPrefixCuts (2^48) 8791130113 10 Manual.Count131072.C067041.packed 64 cuts67041 = true := by
 decide +kernel
def pointBounds67041 : List (Nat × Nat × Nat) := [(8791230464,115283678662935,115284067857709)]
theorem point_links_checked67041 : (cuts67041.take 1).map (fun c => (8791130113-1+2*2^10*c.k,115283538648774+c.lower,115283927843468+c.upper)) = pointBounds67041 := by
 decide +kernel
def cuts67042 : List PrefixCut := [⟨64,181378233,181378344⟩]
theorem checked67042 : checkPrefixCuts (2^48) 8791261185 10 Manual.Count131072.C067042.packed 64 cuts67042 = true := by
 decide +kernel
def cuts67043 : List PrefixCut := [⟨56,159956400,159956494⟩,
⟨64,182272007,182272115⟩]
theorem checked67043 : checkPrefixCuts (2^48) 8791392257 10 Manual.Count131072.C067043.packed 64 cuts67043 = true := by
 decide +kernel
def pointBounds67043 : List (Nat × Nat × Nat) := [(8791506944,115284063157337,115284452352344)]
theorem point_links_checked67043 : (cuts67043.take 1).map (fun c => (8791392257-1+2*2^10*c.k,115283903200937+c.lower,115284292395850+c.upper)) = pointBounds67043 := by
 decide +kernel
def cuts67044 : List PrefixCut := [⟨64,181180737,181180844⟩]
theorem checked67044 : checkPrefixCuts (2^48) 8791523329 10 Manual.Count131072.C067044.packed 64 cuts67044 = true := by
 decide +kernel
def cuts67045 : List PrefixCut := [⟨63,181274088,181274195⟩,
⟨64,184123483,184123592⟩]
theorem checked67045 : checkPrefixCuts (2^48) 8791654401 10 Manual.Count131072.C067045.packed 64 cuts67045 = true := by
 decide +kernel
def pointBounds67045 : List (Nat × Nat × Nat) := [(8791783424,115284447927769,115284837123004)]
theorem point_links_checked67045 : (cuts67045.take 1).map (fun c => (8791654401-1+2*2^10*c.k,115284266653681+c.lower,115284655848809+c.upper)) = pointBounds67045 := by
 decide +kernel
def cuts67046 : List PrefixCut := [⟨64,184793057,184793163⟩]
theorem checked67046 : checkPrefixCuts (2^48) 8791785473 10 Manual.Count131072.C067046.packed 64 cuts67046 = true := by
 decide +kernel
def cuts67047 : List PrefixCut := [⟨64,181812903,181813018⟩]
theorem checked67047 : checkPrefixCuts (2^48) 8791916545 10 Manual.Count131072.C067047.packed 64 cuts67047 = true := by
 decide +kernel
def cuts67048 : List PrefixCut := [⟨6,17383979,17383988⟩,
⟨64,185523884,185523998⟩]
theorem checked67048 : checkPrefixCuts (2^48) 8792047617 10 Manual.Count131072.C067048.packed 64 cuts67048 = true := by
 decide +kernel
def pointBounds67048 : List (Nat × Nat × Nat) := [(8792059904,115284834767103,115285223962570)]
theorem point_links_checked67048 : (cuts67048.take 1).map (fun c => (8792047617-1+2*2^10*c.k,115284817383124+c.lower,115285206578582+c.upper)) = pointBounds67048 := by
 decide +kernel
def cuts67049 : List PrefixCut := [⟨64,184912858,184912967⟩]
theorem checked67049 : checkPrefixCuts (2^48) 8792178689 10 Manual.Count131072.C067049.packed 64 cuts67049 = true := by
 decide +kernel
def cuts67050 : List PrefixCut := [⟨13,36239522,36239545⟩,
⟨64,180716331,180716435⟩]
theorem checked67050 : checkPrefixCuts (2^48) 8792309761 10 Manual.Count131072.C067050.packed 64 cuts67050 = true := by
 decide +kernel
def pointBounds67050 : List (Nat × Nat × Nat) := [(8792336384,115285224059388,115285613255092)]
theorem point_links_checked67050 : (cuts67050.take 1).map (fun c => (8792309761-1+2*2^10*c.k,115285187819866+c.lower,115285577015547+c.upper)) = pointBounds67050 := by
 decide +kernel
def cuts67051 : List PrefixCut := [⟨64,185515576,185515681⟩]
theorem checked67051 : checkPrefixCuts (2^48) 8792440833 10 Manual.Count131072.C067051.packed 64 cuts67051 = true := by
 decide +kernel
def cuts67052 : List PrefixCut := [⟨20,57174735,57174774⟩,
⟨64,182183515,182183631⟩]
theorem checked67052 : checkPrefixCuts (2^48) 8792571905 10 Manual.Count131072.C067052.packed 64 cuts67052 = true := by
 decide +kernel
def pointBounds67052 : List (Nat × Nat × Nat) := [(8792612864,115285611226508,115286000422437)]
theorem point_links_checked67052 : (cuts67052.take 1).map (fun c => (8792571905-1+2*2^10*c.k,115285554051773+c.lower,115285943247663+c.upper)) = pointBounds67052 := by
 decide +kernel
def cuts67053 : List PrefixCut := [⟨64,183397259,183397364⟩]
theorem checked67053 : checkPrefixCuts (2^48) 8792702977 10 Manual.Count131072.C067053.packed 64 cuts67053 = true := by
 decide +kernel
def cuts67054 : List PrefixCut := [⟨27,78428790,78428833⟩,
⟨64,183618623,183618726⟩]
theorem checked67054 : checkPrefixCuts (2^48) 8792834049 10 Manual.Count131072.C067054.packed 64 cuts67054 = true := by
 decide +kernel
def pointBounds67054 : List (Nat × Nat × Nat) := [(8792889344,115285998061337,115286387257491)]
theorem point_links_checked67054 : (cuts67054.take 1).map (fun c => (8792834049-1+2*2^10*c.k,115285919632547+c.lower,115286308828658+c.upper)) = pointBounds67054 := by
 decide +kernel
def cuts67055 : List PrefixCut := [⟨64,184608206,184608317⟩]
theorem checked67055 : checkPrefixCuts (2^48) 8792965121 10 Manual.Count131072.C067055.packed 64 cuts67055 = true := by
 decide +kernel
def cuts67056 : List PrefixCut := [⟨34,97120671,97120724⟩,
⟨64,182300695,182300793⟩]
theorem checked67056 : checkPrefixCuts (2^48) 8793096193 10 Manual.Count131072.C067056.packed 64 cuts67056 = true := by
 decide +kernel
def pointBounds67056 : List (Nat × Nat × Nat) := [(8793165824,115286384980047,115286774176425)]
theorem point_links_checked67056 : (cuts67056.take 1).map (fun c => (8793096193-1+2*2^10*c.k,115286287859376+c.lower,115286677055701+c.upper)) = pointBounds67056 := by
 decide +kernel
def cuts67057 : List PrefixCut := [⟨64,181273657,181273759⟩]
theorem checked67057 : checkPrefixCuts (2^48) 8793227265 10 Manual.Count131072.C067057.packed 64 cuts67057 = true := by
 decide +kernel
def cuts67058 : List PrefixCut := [⟨41,117603965,117604031⟩,
⟨64,182391295,182391401⟩]
theorem checked67058 : checkPrefixCuts (2^48) 8793358337 10 Manual.Count131072.C067058.packed 64 cuts67058 = true := by
 decide +kernel
def pointBounds67058 : List (Nat × Nat × Nat) := [(8793442304,115286769037693,115287158234284)]
theorem point_links_checked67058 : (cuts67058.take 1).map (fun c => (8793358337-1+2*2^10*c.k,115286651433728+c.lower,115287040630253+c.upper)) = pointBounds67058 := by
 decide +kernel
def cuts67059 : List PrefixCut := [⟨64,184757246,184757356⟩]
theorem checked67059 : checkPrefixCuts (2^48) 8793489409 10 Manual.Count131072.C067059.packed 64 cuts67059 = true := by
 decide +kernel
def cuts67060 : List PrefixCut := [⟨48,135877404,135877479⟩,
⟨64,180337307,180337408⟩]
theorem checked67060 : checkPrefixCuts (2^48) 8793620481 10 Manual.Count131072.C067060.packed 64 cuts67060 = true := by
 decide +kernel
def pointBounds67060 : List (Nat × Nat × Nat) := [(8793718784,115287154459673,115287543656489)]
theorem point_links_checked67060 : (cuts67060.take 1).map (fun c => (8793620481-1+2*2^10*c.k,115287018582269+c.lower,115287407779010+c.upper)) = pointBounds67060 := by
 decide +kernel
def cuts67061 : List PrefixCut := [⟨64,185071824,185071933⟩]
theorem checked67061 : checkPrefixCuts (2^48) 8793751553 10 Manual.Count131072.C067061.packed 64 cuts67061 = true := by
 decide +kernel
def cuts67062 : List PrefixCut := [⟨55,158022659,158022749⟩,
⟨64,183596725,183596828⟩]
theorem checked67062 : checkPrefixCuts (2^48) 8793882625 10 Manual.Count131072.C067062.packed 64 cuts67062 = true := by
 decide +kernel
def pointBounds67062 : List (Nat × Nat × Nat) := [(8793995264,115287542014059,115287931211100)]
theorem point_links_checked67062 : (cuts67062.take 1).map (fun c => (8793882625-1+2*2^10*c.k,115287383991400+c.lower,115287773188351+c.upper)) = pointBounds67062 := by
 decide +kernel
def cuts67063 : List PrefixCut := [⟨64,180265211,180265318⟩]
theorem checked67063 : checkPrefixCuts (2^48) 8794013697 10 Manual.Count131072.C067063.packed 64 cuts67063 = true := by
 decide +kernel
def cuts67064 : List PrefixCut := [⟨62,181126750,181126861⟩,
⟨64,187240012,187240127⟩]
theorem checked67064 : checkPrefixCuts (2^48) 8794144769 10 Manual.Count131072.C067064.packed 64 cuts67064 = true := by
 decide +kernel
def pointBounds67064 : List (Nat × Nat × Nat) := [(8794271744,115287928980086,115288318177358)]
theorem point_links_checked67064 : (cuts67064.take 1).map (fun c => (8794144769-1+2*2^10*c.k,115287747853336+c.lower,115288137050497+c.upper)) = pointBounds67064 := by
 decide +kernel
def cuts67065 : List PrefixCut := [⟨64,184292644,184292748⟩]
theorem checked67065 : checkPrefixCuts (2^48) 8794275841 10 Manual.Count131072.C067065.packed 64 cuts67065 = true := by
 decide +kernel
def cuts67066 : List PrefixCut := [⟨64,183681784,183681888⟩]
theorem checked67066 : checkPrefixCuts (2^48) 8794406913 10 Manual.Count131072.C067066.packed 64 cuts67066 = true := by
 decide +kernel
def cuts67067 : List PrefixCut := [⟨5,14082478,14082484⟩,
⟨64,181982768,181982873⟩]
theorem checked67067 : checkPrefixCuts (2^48) 8794537985 10 Manual.Count131072.C067067.packed 64 cuts67067 = true := by
 decide +kernel
def pointBounds67067 : List (Nat × Nat × Nat) := [(8794548224,115288317150254,115288706347744)]
theorem point_links_checked67067 : (cuts67067.take 1).map (fun c => (8794537985-1+2*2^10*c.k,115288303067776+c.lower,115288692265260+c.upper)) = pointBounds67067 := by
 decide +kernel
def cuts67068 : List PrefixCut := [⟨64,182844186,182844293⟩]
theorem checked67068 : checkPrefixCuts (2^48) 8794669057 10 Manual.Count131072.C067068.packed 64 cuts67068 = true := by
 decide +kernel
def cuts67069 : List PrefixCut := [⟨12,34212969,34212991⟩,
⟨64,183225507,183225616⟩]
theorem checked67069 : checkPrefixCuts (2^48) 8794800129 10 Manual.Count131072.C067069.packed 64 cuts67069 = true := by
 decide +kernel
def pointBounds67069 : List (Nat × Nat × Nat) := [(8794824704,115288702107699,115289091305417)]
theorem point_links_checked67069 : (cuts67069.take 1).map (fun c => (8794800129-1+2*2^10*c.k,115288667894730+c.lower,115289057092426+c.upper)) = pointBounds67069 := by
 decide +kernel
def cuts67070 : List PrefixCut := [⟨64,183638842,183638946⟩]
theorem checked67070 : checkPrefixCuts (2^48) 8794931201 10 Manual.Count131072.C067070.packed 64 cuts67070 = true := by
 decide +kernel
def cuts67071 : List PrefixCut := [⟨19,53478133,53478165⟩,
⟨64,182867996,182868106⟩]
theorem checked67071 : checkPrefixCuts (2^48) 8795062273 10 Manual.Count131072.C067071.packed 64 cuts67071 = true := by
 decide +kernel
def pointBounds67071 : List (Nat × Nat × Nat) := [(8795101184,115289088237212,115289477435153)]
theorem point_links_checked67071 : (cuts67071.take 1).map (fun c => (8795062273-1+2*2^10*c.k,115289034759079+c.lower,115289423956988+c.upper)) = pointBounds67071 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000220
