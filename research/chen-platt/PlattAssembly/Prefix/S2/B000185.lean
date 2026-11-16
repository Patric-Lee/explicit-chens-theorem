import PlattAssemblyKernel
import PlattCertificates.Count131072.C015920
import PlattCertificates.Count131072.C015921
import PlattCertificates.Count131072.C015922
import PlattCertificates.Count131072.C015923
import PlattCertificates.Count131072.C015924
import PlattCertificates.Count131072.C015925
import PlattCertificates.Count131072.C015926
import PlattCertificates.Count131072.C015927
import PlattCertificates.Count131072.C015928
import PlattCertificates.Count131072.C015929
import PlattCertificates.Count131072.C015930
import PlattCertificates.Count131072.C015931
import PlattCertificates.Count131072.C015932
import PlattCertificates.Count131072.C015933
import PlattCertificates.Count131072.C015934
import PlattCertificates.Count131072.C015935
import PlattCertificates.Count131072.C015936
import PlattCertificates.Count131072.C015937
import PlattCertificates.Count131072.C015938
import PlattCertificates.Count131072.C015939
import PlattCertificates.Count131072.C015940
import PlattCertificates.Count131072.C015941
import PlattCertificates.Count131072.C015942
import PlattCertificates.Count131072.C015943
import PlattCertificates.Count131072.C015944
import PlattCertificates.Count131072.C015945
import PlattCertificates.Count131072.C015946
import PlattCertificates.Count131072.C015947
import PlattCertificates.Count131072.C015948
import PlattCertificates.Count131072.C015949
import PlattCertificates.Count131072.C015950
import PlattCertificates.Count131072.C015951
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000185
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts15920 : List PrefixCut := [⟨38,245308977,245309136⟩,
⟨102,658230889,658231315⟩,
⟨128,824499975,824500509⟩]
theorem checked15920 : checkPrefixCuts (2^48) 2090598401 9 Manual.Count131072.C015920.packed 128 cuts15920 = true := by
 decide +kernel
def pointBounds15920 : List (Nat × Nat × Nat) := [(2090637312,97049362005380,97049740551189),(2090702848,97049774927292,97050153473368)]
theorem point_links_checked15920 : (cuts15920.take 2).map (fun c => (2090598401-1+2*2^9*c.k,97049116696403+c.lower,97049495242053+c.upper)) = pointBounds15920 := by
 decide +kernel
def cuts15921 : List PrefixCut := [⟨38,240850791,240850949⟩,
⟨102,653073627,653074043⟩,
⟨128,813678178,813678696⟩]
theorem checked15921 : checkPrefixCuts (2^48) 2090729473 9 Manual.Count131072.C015921.packed 128 cuts15921 = true := by
 decide +kernel
def pointBounds15921 : List (Nat × Nat × Nat) := [(2090768384,97050182047169,97050560593511),(2090833920,97050594270005,97050972816605)]
theorem point_links_checked15921 : (cuts15921.take 2).map (fun c => (2090729473-1+2*2^9*c.k,97049941196378+c.lower,97050319742562+c.upper)) = pointBounds15921 := by
 decide +kernel
def cuts15922 : List PrefixCut := [⟨38,246220514,246220671⟩,
⟨102,651955845,651956263⟩,
⟨128,819415611,819416137⟩]
theorem checked15922 : checkPrefixCuts (2^48) 2090860545 9 Manual.Count131072.C015922.packed 128 cuts15922 = true := by
 decide +kernel
def pointBounds15922 : List (Nat × Nat × Nat) := [(2090899456,97051001095070,97051379641929),(2090964992,97051406830401,97051785377521)]
theorem point_links_checked15922 : (cuts15922.take 2).map (fun c => (2090860545-1+2*2^9*c.k,97050754874556+c.lower,97051133421258+c.upper)) = pointBounds15922 := by
 decide +kernel
def cuts15923 : List PrefixCut := [⟨38,241089811,241089962⟩,
⟨102,656491622,656492038⟩,
⟨128,820171945,820172465⟩]
theorem checked15923 : checkPrefixCuts (2^48) 2090991617 9 Manual.Count131072.C015923.packed 128 cuts15923 = true := by
 decide +kernel
def pointBounds15923 : List (Nat × Nat × Nat) := [(2091030528,97051815379978,97052193927357),(2091096064,97052230781789,97052609329433)]
theorem point_links_checked15923 : (cuts15923.take 2).map (fun c => (2090991617-1+2*2^9*c.k,97051574290167+c.lower,97051952837395+c.upper)) = pointBounds15923 := by
 decide +kernel
def cuts15924 : List PrefixCut := [⟨38,246458892,246459050⟩,
⟨102,657123625,657124046⟩,
⟨128,827254345,827254874⟩]
theorem checked15924 : checkPrefixCuts (2^48) 2091122689 9 Manual.Count131072.C015924.packed 128 cuts15924 = true := by
 decide +kernel
def pointBounds15924 : List (Nat × Nat × Nat) := [(2091161600,97052640921004,97053019468910),(2091227136,97053051585737,97053430133906)]
theorem point_links_checked15924 : (cuts15924.take 2).map (fun c => (2091122689-1+2*2^9*c.k,97052394462112+c.lower,97052773009860+c.upper)) = pointBounds15924 := by
 decide +kernel
def cuts15925 : List PrefixCut := [⟨38,240521207,240521364⟩,
⟨102,653448259,653448679⟩,
⟨128,815493015,815493537⟩]
theorem checked15925 : checkPrefixCuts (2^48) 2091253761 9 Manual.Count131072.C015925.packed 128 cuts15925 = true := by
 decide +kernel
def pointBounds15925 : List (Nat × Nat × Nat) := [(2091292672,97053462237664,97053840786098),(2091358208,97053875164716,97054253713413)]
theorem point_links_checked15925 : (cuts15925.take 2).map (fun c => (2091253761-1+2*2^9*c.k,97053221716457+c.lower,97053600264734+c.upper)) = pointBounds15925 := by
 decide +kernel
def cuts15926 : List PrefixCut := [⟨38,244812963,244813120⟩,
⟨102,652196324,652196743⟩,
⟨128,817057106,817057632⟩]
theorem checked15926 : checkPrefixCuts (2^48) 2091384833 9 Manual.Count131072.C015926.packed 128 cuts15926 = true := by
 decide +kernel
def pointBounds15926 : List (Nat × Nat × Nat) := [(2091423744,97054282022435,97054660571391),(2091489280,97054689405796,97055067955014)]
theorem point_links_checked15926 : (cuts15926.take 2).map (fun c => (2091384833-1+2*2^9*c.k,97054037209472+c.lower,97054415758271+c.upper)) = pointBounds15926 := by
 decide +kernel
def cuts15927 : List PrefixCut := [⟨38,239549053,239549211⟩,
⟨102,648521701,648522123⟩,
⟨128,820369882,820370412⟩]
theorem checked15927 : checkPrefixCuts (2^48) 2091515905 9 Manual.Count131072.C015927.packed 128 cuts15927 = true := by
 decide +kernel
def pointBounds15927 : List (Nat × Nat × Nat) := [(2091554816,97055093815631,97055472365114),(2091620352,97055502788279,97055881338026)]
theorem point_links_checked15927 : (cuts15927.take 2).map (fun c => (2091515905-1+2*2^9*c.k,97054854266578+c.lower,97055232815903+c.upper)) = pointBounds15927 := by
 decide +kernel
def cuts15928 : List PrefixCut := [⟨38,241552559,241552715⟩,
⟨102,661265023,661265450⟩,
⟨128,827854460,827854993⟩]
theorem checked15928 : checkPrefixCuts (2^48) 2091646977 9 Manual.Count131072.C015928.packed 128 cuts15928 = true := by
 decide +kernel
def pointBounds15928 : List (Nat × Nat × Nat) := [(2091685888,97055916189019,97056294739030),(2091751424,97056335901483,97056714451765)]
theorem point_links_checked15928 : (cuts15928.take 2).map (fun c => (2091646977-1+2*2^9*c.k,97055674636460+c.lower,97056053186315+c.upper)) = pointBounds15928 := by
 decide +kernel
def cuts15929 : List PrefixCut := [⟨38,246919869,246920024⟩,
⟨102,662030950,662031370⟩,
⟨128,827668051,827668579⟩]
theorem checked15929 : checkPrefixCuts (2^48) 2091778049 9 Manual.Count131072.C015929.packed 128 cuts15929 = true := by
 decide +kernel
def pointBounds15929 : List (Nat × Nat × Nat) := [(2091816960,97056749410789,97057127961332),(2091882496,97057164521870,97057543072678)]
theorem point_links_checked15929 : (cuts15929.take 2).map (fun c => (2091778049-1+2*2^9*c.k,97056502490920+c.lower,97056881041308+c.upper)) = pointBounds15929 := by
 decide +kernel
def cuts15930 : List PrefixCut := [⟨38,240311305,240311461⟩,
⟨102,661047528,661047956⟩,
⟨128,826674267,826674802⟩]
theorem checked15930 : checkPrefixCuts (2^48) 2091909121 9 Manual.Count131072.C015930.packed 128 cuts15930 = true := by
 decide +kernel
def pointBounds15930 : List (Nat × Nat × Nat) := [(2091948032,97057570470276,97057949021348),(2092013568,97057991206499,97058369757843)]
theorem point_links_checked15930 : (cuts15930.take 2).map (fun c => (2091909121-1+2*2^9*c.k,97057330158971+c.lower,97057708709887+c.upper)) = pointBounds15930 := by
 decide +kernel
def cuts15931 : List PrefixCut := [⟨38,250656155,250656309⟩,
⟨102,663428065,663428487⟩,
⟨128,825277357,825277885⟩]
theorem checked15931 : checkPrefixCuts (2^48) 2092040193 9 Manual.Count131072.C015931.packed 128 cuts15931 = true := by
 decide +kernel
def pointBounds15931 : List (Nat × Nat × Nat) := [(2092079104,97058407489393,97058786040998),(2092144640,97058820261303,97059198813176)]
theorem point_links_checked15931 : (cuts15931.take 2).map (fun c => (2092040193-1+2*2^9*c.k,97058156833238+c.lower,97058535384689+c.upper)) = pointBounds15931 := by
 decide +kernel
def cuts15932 : List PrefixCut := [⟨38,243913710,243913868⟩,
⟨102,655449026,655449449⟩,
⟨128,819978765,819979297⟩]
theorem checked15932 : checkPrefixCuts (2^48) 2092171265 9 Manual.Count131072.C015932.packed 128 cuts15932 = true := by
 decide +kernel
def pointBounds15932 : List (Nat × Nat × Nat) := [(2092210176,97059226024305,97059604576442),(2092275712,97059637559621,97060016112023)]
theorem point_links_checked15932 : (cuts15932.take 2).map (fun c => (2092171265-1+2*2^9*c.k,97058982110595+c.lower,97059360662574+c.upper)) = pointBounds15932 := by
 decide +kernel
def cuts15933 : List PrefixCut := [⟨38,245243628,245243788⟩,
⟨102,653120935,653121361⟩,
⟨128,818043937,818044469⟩]
theorem checked15933 : checkPrefixCuts (2^48) 2092302337 9 Manual.Count131072.C015933.packed 128 cuts15933 = true := by
 decide +kernel
def pointBounds15933 : List (Nat × Nat × Nat) := [(2092341248,97060047332988,97060425885659),(2092406784,97060455210295,97060833763232)]
theorem point_links_checked15933 : (cuts15933.take 2).map (fun c => (2092302337-1+2*2^9*c.k,97059802089360+c.lower,97060180641871+c.upper)) = pointBounds15933 := by
 decide +kernel
def cuts15934 : List PrefixCut := [⟨38,247649676,247649841⟩,
⟨102,656443033,656443463⟩,
⟨128,822700832,822701365⟩]
theorem checked15934 : checkPrefixCuts (2^48) 2092433409 9 Manual.Count131072.C015934.packed 128 cuts15934 = true := by
 decide +kernel
def pointBounds15934 : List (Nat × Nat × Nat) := [(2092472320,97060867782973,97061246336181),(2092537856,97061276576330,97061655129803)]
theorem point_links_checked15934 : (cuts15934.take 2).map (fun c => (2092433409-1+2*2^9*c.k,97060620133297+c.lower,97060998686340+c.upper)) = pointBounds15934 := by
 decide +kernel
def cuts15935 : List PrefixCut := [⟨38,236873323,236873477⟩,
⟨102,639991777,639992194⟩,
⟨128,811350338,811350869⟩]
theorem checked15935 : checkPrefixCuts (2^48) 2092564481 9 Manual.Count131072.C015935.packed 128 cuts15935 = true := by
 decide +kernel
def pointBounds15935 : List (Nat × Nat × Nat) := [(2092603392,97061679707452,97062058261182),(2092668928,97062082825906,97062461379899)]
theorem point_links_checked15935 : (cuts15935.take 2).map (fun c => (2092564481-1+2*2^9*c.k,97061442834129+c.lower,97061821387705+c.upper)) = pointBounds15935 := by
 decide +kernel
def cuts15936 : List PrefixCut := [⟨38,241700536,241700690⟩,
⟨102,642776282,642776693⟩,
⟨128,815603570,815604091⟩]
theorem checked15936 : checkPrefixCuts (2^48) 2092695553 9 Manual.Count131072.C015936.packed 128 cuts15936 = true := by
 decide +kernel
def pointBounds15936 : List (Nat × Nat × Nat) := [(2092734464,97062495885003,97062874439264),(2092800000,97062896960749,97063275515267)]
theorem point_links_checked15936 : (cuts15936.take 2).map (fun c => (2092695553-1+2*2^9*c.k,97062254184467+c.lower,97062632738574+c.upper)) = pointBounds15936 := by
 decide +kernel
def cuts15937 : List PrefixCut := [⟨38,242895852,242896005⟩,
⟨102,656185097,656185519⟩,
⟨128,823756554,823757085⟩]
theorem checked15937 : checkPrefixCuts (2^48) 2092826625 9 Manual.Count131072.C015937.packed 128 cuts15937 = true := by
 decide +kernel
def pointBounds15937 : List (Nat × Nat × Nat) := [(2092865536,97063312683889,97063691238670),(2092931072,97063725973134,97064104528184)]
theorem point_links_checked15937 : (cuts15937.take 2).map (fun c => (2092826625-1+2*2^9*c.k,97063069788037+c.lower,97063448342665+c.upper)) = pointBounds15937 := by
 decide +kernel
def cuts15938 : List PrefixCut := [⟨38,245973791,245973948⟩,
⟨102,660447488,660447912⟩,
⟨128,825722294,825722825⟩]
theorem checked15938 : checkPrefixCuts (2^48) 2092957697 9 Manual.Count131072.C015938.packed 128 cuts15938 = true := by
 decide +kernel
def pointBounds15938 : List (Nat × Nat × Nat) := [(2092996608,97064139518382,97064518073698),(2093062144,97064553992079,97064932547662)]
theorem point_links_checked15938 : (cuts15938.take 2).map (fun c => (2092957697-1+2*2^9*c.k,97063893544591+c.lower,97064272099750+c.upper)) = pointBounds15938 := by
 decide +kernel
def cuts15939 : List PrefixCut := [⟨38,242462027,242462184⟩,
⟨102,655027138,655027561⟩,
⟨128,822174190,822174718⟩]
theorem checked15939 : checkPrefixCuts (2^48) 2093088769 9 Manual.Count131072.C015939.packed 128 cuts15939 = true := by
 decide +kernel
def pointBounds15939 : List (Nat × Nat × Nat) := [(2093127680,97064961728912,97065340284759),(2093193216,97065374294023,97065752850136)]
theorem point_links_checked15939 : (cuts15939.take 2).map (fun c => (2093088769-1+2*2^9*c.k,97064719266885+c.lower,97065097822575+c.upper)) = pointBounds15939 := by
 decide +kernel
def cuts15940 : List PrefixCut := [⟨38,244463838,244463999⟩,
⟨102,657137537,657137961⟩,
⟨128,820240249,820240780⟩]
theorem checked15940 : checkPrefixCuts (2^48) 2093219841 9 Manual.Count131072.C015940.packed 128 cuts15940 = true := by
 decide +kernel
def pointBounds15940 : List (Nat × Nat × Nat) := [(2093258752,97065785904913,97066164461292),(2093324288,97066198578612,97066577135254)]
theorem point_links_checked15940 : (cuts15940.take 2).map (fun c => (2093219841-1+2*2^9*c.k,97065541441075+c.lower,97065919997293+c.upper)) = pointBounds15940 := by
 decide +kernel
def cuts15941 : List PrefixCut := [⟨38,241221512,241221670⟩,
⟨102,647012144,647012562⟩,
⟨128,818575237,818575762⟩]
theorem checked15941 : checkPrefixCuts (2^48) 2093350913 9 Manual.Count131072.C015941.packed 128 cuts15941 = true := by
 decide +kernel
def pointBounds15941 : List (Nat × Nat × Nat) := [(2093389824,97066602902836,97066981459743),(2093455360,97067008693468,97067387250635)]
theorem point_links_checked15941 : (cuts15941.take 2).map (fun c => (2093350913-1+2*2^9*c.k,97066361681324+c.lower,97066740238073+c.upper)) = pointBounds15941 := by
 decide +kernel
def cuts15942 : List PrefixCut := [⟨38,245777770,245777927⟩,
⟨102,661492097,661492524⟩,
⟨128,828338859,828339391⟩]
theorem checked15942 : checkPrefixCuts (2^48) 2093481985 9 Manual.Count131072.C015942.packed 128 cuts15942 = true := by
 decide +kernel
def pointBounds15942 : List (Nat × Nat × Nat) := [(2093520896,97067426034331,97067804591762),(2093586432,97067841748658,97068220306359)]
theorem point_links_checked15942 : (cuts15942.take 2).map (fun c => (2093481985-1+2*2^9*c.k,97067180256561+c.lower,97067558813835+c.upper)) = pointBounds15942 := by
 decide +kernel
def cuts15943 : List PrefixCut := [⟨38,244417947,244418101⟩,
⟨102,653653201,653653622⟩,
⟨128,817666335,817666860⟩]
theorem checked15943 : checkPrefixCuts (2^48) 2093613057 9 Manual.Count131072.C015943.packed 128 cuts15943 = true := by
 decide +kernel
def pointBounds15943 : List (Nat × Nat × Nat) := [(2093651968,97068253013367,97068631571327),(2093717504,97068662248621,97069040806848)]
theorem point_links_checked15943 : (cuts15943.take 2).map (fun c => (2093613057-1+2*2^9*c.k,97068008595420+c.lower,97068387153226+c.upper)) = pointBounds15943 := by
 decide +kernel
def cuts15944 : List PrefixCut := [⟨38,243327174,243327331⟩,
⟨102,660602752,660603180⟩,
⟨128,828504047,828504581⟩]
theorem checked15944 : checkPrefixCuts (2^48) 2093744129 9 Manual.Count131072.C015944.packed 128 cuts15944 = true := by
 decide +kernel
def pointBounds15944 : List (Nat × Nat × Nat) := [(2093783040,97069069588929,97069448147417),(2093848576,97069486864507,97069865423266)]
theorem point_links_checked15944 : (cuts15944.take 2).map (fun c => (2093744129-1+2*2^9*c.k,97068826261755+c.lower,97069204820086+c.upper)) = pointBounds15944 := by
 decide +kernel
def cuts15945 : List PrefixCut := [⟨38,242505355,242505513⟩,
⟨102,646446833,646447248⟩,
⟨128,812858985,812859508⟩]
theorem checked15945 : checkPrefixCuts (2^48) 2093875201 9 Manual.Count131072.C015945.packed 128 cuts15945 = true := by
 decide +kernel
def pointBounds15945 : List (Nat × Nat × Nat) := [(2093914112,97069897271157,97070275830180),(2093979648,97070301212635,97070679771915)]
theorem point_links_checked15945 : (cuts15945.take 2).map (fun c => (2093875201-1+2*2^9*c.k,97069654765802+c.lower,97070033324667+c.upper)) = pointBounds15945 := by
 decide +kernel
def cuts15946 : List PrefixCut := [⟨38,231871096,231871250⟩,
⟨102,643180090,643180508⟩,
⟨128,808103314,808103840⟩]
theorem checked15946 : checkPrefixCuts (2^48) 2094006273 9 Manual.Count131072.C015946.packed 128 cuts15946 = true := by
 decide +kernel
def pointBounds15946 : List (Nat × Nat × Nat) := [(2094045184,97070699495883,97071078055425),(2094110720,97071110804877,97071489364683)]
theorem point_links_checked15946 : (cuts15946.take 2).map (fun c => (2094006273-1+2*2^9*c.k,97070467624787+c.lower,97070846184175+c.upper)) = pointBounds15946 := by
 decide +kernel
def cuts15947 : List PrefixCut := [⟨38,245028805,245028965⟩,
⟨102,653086384,653086812⟩,
⟨128,824181836,824182376⟩]
theorem checked15947 : checkPrefixCuts (2^48) 2094137345 9 Manual.Count131072.C015947.packed 128 cuts15947 = true := by
 decide +kernel
def pointBounds15947 : List (Nat × Nat × Nat) := [(2094176256,97071520756906,97071899316980),(2094241792,97071928814485,97072307374827)]
theorem point_links_checked15947 : (cuts15947.take 2).map (fun c => (2094137345-1+2*2^9*c.k,97071275728101+c.lower,97071654288015+c.upper)) = pointBounds15947 := by
 decide +kernel
def cuts15948 : List PrefixCut := [⟨38,243266215,243266376⟩,
⟨102,654120573,654121000⟩,
⟨128,822786223,822786757⟩]
theorem checked15948 : checkPrefixCuts (2^48) 2094268417 9 Manual.Count131072.C015948.packed 128 cuts15948 = true := by
 decide +kernel
def pointBounds15948 : List (Nat × Nat × Nat) := [(2094307328,97072343176152,97072721736767),(2094372864,97072754030510,97073132591391)]
theorem point_links_checked15948 : (cuts15948.take 2).map (fun c => (2094268417-1+2*2^9*c.k,97072099909937+c.lower,97072478470391+c.upper)) = pointBounds15948 := by
 decide +kernel
def cuts15949 : List PrefixCut := [⟨38,249701872,249702032⟩,
⟨102,661874453,661874881⟩,
⟨128,827707430,827707966⟩]
theorem checked15949 : checkPrefixCuts (2^48) 2094399489 9 Manual.Count131072.C015949.packed 128 cuts15949 = true := by
 decide +kernel
def pointBounds15949 : List (Nat × Nat × Nat) := [(2094438400,97073172398032,97073550959180),(2094503936,97073584570613,97073963132029)]
theorem point_links_checked15949 : (cuts15949.take 2).map (fun c => (2094399489-1+2*2^9*c.k,97072922696160+c.lower,97073301257148+c.upper)) = pointBounds15949 := by
 decide +kernel
def cuts15950 : List PrefixCut := [⟨38,240951260,240951416⟩,
⟨102,644094492,644094912⟩,
⟨128,808842067,808842596⟩]
theorem checked15950 : checkPrefixCuts (2^48) 2094530561 9 Manual.Count131072.C015950.packed 128 cuts15950 = true := by
 decide +kernel
def pointBounds15950 : List (Nat × Nat × Nat) := [(2094569472,97073991354850,97074369916530),(2094635008,97074394498082,97074773060026)]
theorem point_links_checked15950 : (cuts15950.take 2).map (fun c => (2094530561-1+2*2^9*c.k,97073750403590+c.lower,97074128965114+c.upper)) = pointBounds15950 := by
 decide +kernel
def cuts15951 : List PrefixCut := [⟨38,250880054,250880213⟩,
⟨102,666226004,666226435⟩,
⟨128,835666212,835666751⟩]
theorem checked15951 : checkPrefixCuts (2^48) 2094661633 9 Manual.Count131072.C015951.packed 128 cuts15951 = true := by
 decide +kernel
def pointBounds15951 : List (Nat × Nat × Nat) := [(2094700544,97074810125711,97075188687923),(2094766080,97075225471661,97075604034145)]
theorem point_links_checked15951 : (cuts15951.take 2).map (fun c => (2094661633-1+2*2^9*c.k,97074559245657+c.lower,97074937807710+c.upper)) = pointBounds15951 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000185
