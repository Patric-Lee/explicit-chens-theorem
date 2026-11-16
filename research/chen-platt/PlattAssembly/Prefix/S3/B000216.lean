import PlattAssemblyKernel
import PlattCertificates.Count131072.C026912
import PlattCertificates.Count131072.C026913
import PlattCertificates.Count131072.C026914
import PlattCertificates.Count131072.C026915
import PlattCertificates.Count131072.C026916
import PlattCertificates.Count131072.C026917
import PlattCertificates.Count131072.C026918
import PlattCertificates.Count131072.C026919
import PlattCertificates.Count131072.C026920
import PlattCertificates.Count131072.C026921
import PlattCertificates.Count131072.C026922
import PlattCertificates.Count131072.C026923
import PlattCertificates.Count131072.C026924
import PlattCertificates.Count131072.C026925
import PlattCertificates.Count131072.C026926
import PlattCertificates.Count131072.C026927
import PlattCertificates.Count131072.C026928
import PlattCertificates.Count131072.C026929
import PlattCertificates.Count131072.C026930
import PlattCertificates.Count131072.C026931
import PlattCertificates.Count131072.C026932
import PlattCertificates.Count131072.C026933
import PlattCertificates.Count131072.C026934
import PlattCertificates.Count131072.C026935
import PlattCertificates.Count131072.C026936
import PlattCertificates.Count131072.C026937
import PlattCertificates.Count131072.C026938
import PlattCertificates.Count131072.C026939
import PlattCertificates.Count131072.C026940
import PlattCertificates.Count131072.C026941
import PlattCertificates.Count131072.C026942
import PlattCertificates.Count131072.C026943
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000216
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts26912 : List PrefixCut := [⟨40,148016200,148016283⟩,
⟨128,479671607,479671879⟩]
theorem checked26912 : checkPrefixCuts (2^48) 3531341825 9 Manual.Count131072.C026912.packed 128 cuts26912 = true := by
 decide +kernel
def pointBounds26912 : List (Nat × Nat × Nat) := [(3531382784,103842243837809,103842626382982)]
theorem point_links_checked26912 : (cuts26912.take 1).map (fun c => (3531341825-1+2*2^9*c.k,103842095821609+c.lower,103842478366699+c.upper)) = pointBounds26912 := by
 decide +kernel
def cuts26913 : List PrefixCut := [⟨20,74922182,74922223⟩,
⟨128,477103344,477103610⟩]
theorem checked26913 : checkPrefixCuts (2^48) 3531472897 9 Manual.Count131072.C026913.packed 128 cuts26913 = true := by
 decide +kernel
def pointBounds26913 : List (Nat × Nat × Nat) := [(3531493376,103842650415398,103843032960801),(3531603968,103843052596560,103843435142188)]
theorem point_links_checked26913 : (cuts26913.take 2).map (fun c => (3531472897-1+2*2^9*c.k,103842575493216+c.lower,103842958038578+c.upper)) = pointBounds26913 := by
 decide +kernel
def cuts26914 : List PrefixCut := [⟨108,400574505,400574730⟩,
⟨128,473977274,473977538⟩]
theorem checked26914 : checkPrefixCuts (2^48) 3531603969 9 Manual.Count131072.C026914.packed 128 cuts26914 = true := by
 decide +kernel
def pointBounds26914 : List (Nat × Nat × Nat) := [(3531714560,103843453171065,103843835716918)]
theorem point_links_checked26914 : (cuts26914.take 1).map (fun c => (3531603969-1+2*2^9*c.k,103843052596560+c.lower,103843435142188+c.upper)) = pointBounds26914 := by
 decide +kernel
def cuts26915 : List PrefixCut := [⟨88,326681056,326681240⟩,
⟨128,476828819,476829090⟩]
theorem checked26915 : checkPrefixCuts (2^48) 3531735041 9 Manual.Count131072.C026915.packed 128 cuts26915 = true := by
 decide +kernel
def pointBounds26915 : List (Nat × Nat × Nat) := [(3531825152,103843853254890,103844235800966)]
theorem point_links_checked26915 : (cuts26915.take 1).map (fun c => (3531735041-1+2*2^9*c.k,103843526573834+c.lower,103843909119726+c.upper)) = pointBounds26915 := by
 decide +kernel
def cuts26916 : List PrefixCut := [⟨68,253191086,253191232⟩,
⟨128,473065564,473065834⟩]
theorem checked26916 : checkPrefixCuts (2^48) 3531866113 9 Manual.Count131072.C026916.packed 128 cuts26916 = true := by
 decide +kernel
def pointBounds26916 : List (Nat × Nat × Nat) := [(3531935744,103844256593739,103844639140048)]
theorem point_links_checked26916 : (cuts26916.take 1).map (fun c => (3531866113-1+2*2^9*c.k,103844003402653+c.lower,103844385948816+c.upper)) = pointBounds26916 := by
 decide +kernel
def cuts26917 : List PrefixCut := [⟨48,176837203,176837302⟩,
⟨128,474243305,474243574⟩]
theorem checked26917 : checkPrefixCuts (2^48) 3531997185 9 Manual.Count131072.C026917.packed 128 cuts26917 = true := by
 decide +kernel
def pointBounds26917 : List (Nat × Nat × Nat) := [(3532046336,103844653305420,103845035851952)]
theorem point_links_checked26917 : (cuts26917.take 1).map (fun c => (3531997185-1+2*2^9*c.k,103844476468217+c.lower,103844859014650+c.upper)) = pointBounds26917 := by
 decide +kernel
def cuts26918 : List PrefixCut := [⟨28,105668364,105668421⟩,
⟨128,482911770,482912037⟩]
theorem checked26918 : checkPrefixCuts (2^48) 3532128257 9 Manual.Count131072.C026918.packed 128 cuts26918 = true := by
 decide +kernel
def pointBounds26918 : List (Nat × Nat × Nat) := [(3532156928,103845056379886,103845438926645)]
theorem point_links_checked26918 : (cuts26918.take 1).map (fun c => (3532128257-1+2*2^9*c.k,103844950711522+c.lower,103845333258224+c.upper)) = pointBounds26918 := by
 decide +kernel
def cuts26919 : List PrefixCut := [⟨8,30360686,30360703⟩,
⟨116,432055279,432055523⟩,
⟨128,478112693,478112962⟩]
theorem checked26919 : checkPrefixCuts (2^48) 3532259329 9 Manual.Count131072.C026919.packed 128 cuts26919 = true := by
 decide +kernel
def pointBounds26919 : List (Nat × Nat × Nat) := [(3532267520,103845463983978,103845846530964),(3532378112,103845865678571,103846248225784)]
theorem point_links_checked26919 : (cuts26919.take 2).map (fun c => (3532259329-1+2*2^9*c.k,103845433623292+c.lower,103845816170261+c.upper)) = pointBounds26919 := by
 decide +kernel
def cuts26920 : List PrefixCut := [⟨96,355465249,355465449⟩,
⟨128,472596883,472597148⟩]
theorem checked26920 : checkPrefixCuts (2^48) 3532390401 9 Manual.Count131072.C026920.packed 128 cuts26920 = true := by
 decide +kernel
def pointBounds26920 : List (Nat × Nat × Nat) := [(3532488704,103846267201234,103846649748672)]
theorem point_links_checked26920 : (cuts26920.take 1).map (fun c => (3532390401-1+2*2^9*c.k,103845911735985+c.lower,103846294283223+c.upper)) = pointBounds26920 := by
 decide +kernel
def cuts26921 : List PrefixCut := [⟨76,285095542,285095698⟩,
⟨128,473296550,473296811⟩]
theorem checked26921 : checkPrefixCuts (2^48) 3532521473 9 Manual.Count131072.C026921.packed 128 cuts26921 = true := by
 decide +kernel
def pointBounds26921 : List (Nat × Nat × Nat) := [(3532599296,103846669428410,103847051976069)]
theorem point_links_checked26921 : (cuts26921.take 1).map (fun c => (3532521473-1+2*2^9*c.k,103846384332868+c.lower,103846766880371+c.upper)) = pointBounds26921 := by
 decide +kernel
def cuts26922 : List PrefixCut := [⟨56,208117386,208117505⟩,
⟨128,471844712,471844974⟩]
theorem checked26922 : checkPrefixCuts (2^48) 3532652545 9 Manual.Count131072.C026922.packed 128 cuts26922 = true := by
 decide +kernel
def pointBounds26922 : List (Nat × Nat × Nat) := [(3532709888,103847065746804,103847448294687)]
theorem point_links_checked26922 : (cuts26922.take 1).map (fun c => (3532652545-1+2*2^9*c.k,103846857629418+c.lower,103847240177182+c.upper)) = pointBounds26922 := by
 decide +kernel
def cuts26923 : List PrefixCut := [⟨36,135765678,135765752⟩,
⟨128,479396276,479396542⟩]
theorem checked26923 : checkPrefixCuts (2^48) 3532783617 9 Manual.Count131072.C026923.packed 128 cuts26923 = true := by
 decide +kernel
def pointBounds26923 : List (Nat × Nat × Nat) := [(3532820480,103847465239808,103847847787908)]
theorem point_links_checked26923 : (cuts26923.take 1).map (fun c => (3532783617-1+2*2^9*c.k,103847329474130+c.lower,103847712022156+c.upper)) = pointBounds26923 := by
 decide +kernel
def cuts26924 : List PrefixCut := [⟨16,61905114,61905148⟩,
⟨124,462408843,462409102⟩,
⟨128,476828974,476829241⟩]
theorem checked26924 : checkPrefixCuts (2^48) 3532914689 9 Manual.Count131072.C026924.packed 128 cuts26924 = true := by
 decide +kernel
def pointBounds26924 : List (Nat × Nat × Nat) := [(3532931072,103847870775520,103848253323846),(3533041664,103848271279249,103848653827800)]
theorem point_links_checked26924 : (cuts26924.take 2).map (fun c => (3532914689-1+2*2^9*c.k,103847808870406+c.lower,103848191418698+c.upper)) = pointBounds26924 := by
 decide +kernel
def cuts26925 : List PrefixCut := [⟨104,386947471,386947689⟩,
⟨128,474261975,474262243⟩]
theorem checked26925 : checkPrefixCuts (2^48) 3533045761 9 Manual.Count131072.C026925.packed 128 cuts26925 = true := by
 decide +kernel
def pointBounds26925 : List (Nat × Nat × Nat) := [(3533152256,103848672646851,103849055195628)]
theorem point_links_checked26925 : (cuts26925.take 1).map (fun c => (3533045761-1+2*2^9*c.k,103848285699380+c.lower,103848668247939+c.upper)) = pointBounds26925 := by
 decide +kernel
def cuts26926 : List PrefixCut := [⟨84,316191435,316191610⟩,
⟨128,475598687,475598951⟩]
theorem checked26926 : checkPrefixCuts (2^48) 3533176833 9 Manual.Count131072.C026926.packed 128 cuts26926 = true := by
 decide +kernel
def pointBounds26926 : List (Nat × Nat × Nat) := [(3533262848,103849076152790,103849458701792)]
theorem point_links_checked26926 : (cuts26926.take 1).map (fun c => (3533176833-1+2*2^9*c.k,103848759961355+c.lower,103849142510182+c.upper)) = pointBounds26926 := by
 decide +kernel
def cuts26927 : List PrefixCut := [⟨64,237394385,237394515⟩,
⟨128,475580951,475581213⟩]
theorem checked26927 : checkPrefixCuts (2^48) 3533307905 9 Manual.Count131072.C026927.packed 128 cuts26927 = true := by
 decide +kernel
def pointBounds26927 : List (Nat × Nat × Nat) := [(3533373440,103849472954427,103849855503648)]
theorem point_links_checked26927 : (cuts26927.take 1).map (fun c => (3533307905-1+2*2^9*c.k,103849235560042+c.lower,103849618109133+c.upper)) = pointBounds26927 := by
 decide +kernel
def cuts26928 : List PrefixCut := [⟨44,160992488,160992576⟩,
⟨128,470544846,470545108⟩]
theorem checked26928 : checkPrefixCuts (2^48) 3533438977 9 Manual.Count131072.C026928.packed 128 cuts26928 = true := by
 decide +kernel
def pointBounds26928 : List (Nat × Nat × Nat) := [(3533484032,103849872133481,103850254682922)]
theorem point_links_checked26928 : (cuts26928.take 1).map (fun c => (3533438977-1+2*2^9*c.k,103849711140993+c.lower,103850093690346+c.upper)) = pointBounds26928 := by
 decide +kernel
def cuts26929 : List PrefixCut := [⟨24,90490461,90490509⟩,
⟨128,476182961,476183222⟩]
theorem checked26929 : checkPrefixCuts (2^48) 3533570049 9 Manual.Count131072.C026929.packed 128 cuts26929 = true := by
 decide +kernel
def pointBounds26929 : List (Nat × Nat × Nat) := [(3533594624,103850272176300,103850654725963)]
theorem point_links_checked26929 : (cuts26929.take 1).map (fun c => (3533570049-1+2*2^9*c.k,103850181685839+c.lower,103850564235454+c.upper)) = pointBounds26929 := by
 decide +kernel
def cuts26930 : List PrefixCut := [⟨4,14656403,14656412⟩,
⟨112,415311424,415311654⟩,
⟨128,473377476,473377740⟩]
theorem checked26930 : checkPrefixCuts (2^48) 3533701121 9 Manual.Count131072.C026930.packed 128 cuts26930 = true := by
 decide +kernel
def pointBounds26930 : List (Nat × Nat × Nat) := [(3533705216,103850672525203,103851055075088),(3533815808,103851073180224,103851455730330)]
theorem point_links_checked26930 : (cuts26930.take 2).map (fun c => (3533701121-1+2*2^9*c.k,103850657868800+c.lower,103851040418676+c.upper)) = pointBounds26930 := by
 decide +kernel
def cuts26931 : List PrefixCut := [⟨92,350700692,350700884⟩,
⟨128,482519650,482519914⟩]
theorem checked26931 : checkPrefixCuts (2^48) 3533832193 9 Manual.Count131072.C026931.packed 128 cuts26931 = true := by
 decide +kernel
def pointBounds26931 : List (Nat × Nat × Nat) := [(3533926400,103851481946968,103851864497300)]
theorem point_links_checked26931 : (cuts26931.take 1).map (fun c => (3533832193-1+2*2^9*c.k,103851131246276+c.lower,103851513796416+c.upper)) = pointBounds26931 := by
 decide +kernel
def cuts26932 : List PrefixCut := [⟨72,266899352,266899504⟩,
⟨128,474377707,474377975⟩]
theorem checked26932 : checkPrefixCuts (2^48) 3533963265 9 Manual.Count131072.C026932.packed 128 cuts26932 = true := by
 decide +kernel
def pointBounds26932 : List (Nat × Nat × Nat) := [(3534036992,103851880665278,103852263215834)]
theorem point_links_checked26932 : (cuts26932.take 1).map (fun c => (3533963265-1+2*2^9*c.k,103851613765926+c.lower,103851996316330+c.upper)) = pointBounds26932 := by
 decide +kernel
def cuts26933 : List PrefixCut := [⟨52,192103617,192103724⟩,
⟨128,479935115,479935382⟩]
theorem checked26933 : checkPrefixCuts (2^48) 3534094337 9 Manual.Count131072.C026933.packed 128 cuts26933 = true := by
 decide +kernel
def pointBounds26933 : List (Nat × Nat × Nat) := [(3534147584,103852280247250,103852662798029)]
theorem point_links_checked26933 : (cuts26933.take 1).map (fun c => (3534094337-1+2*2^9*c.k,103852088143633+c.lower,103852470694305+c.upper)) = pointBounds26933 := by
 decide +kernel
def cuts26934 : List PrefixCut := [⟨32,117711212,117711278⟩,
⟨128,471077160,471077432⟩]
theorem checked26934 : checkPrefixCuts (2^48) 3534225409 9 Manual.Count131072.C026934.packed 128 cuts26934 = true := by
 decide +kernel
def pointBounds26934 : List (Nat × Nat × Nat) := [(3534258176,103852685789960,103853068340965)]
theorem point_links_checked26934 : (cuts26934.take 1).map (fun c => (3534225409-1+2*2^9*c.k,103852568078748+c.lower,103852950629687+c.upper)) = pointBounds26934 := by
 decide +kernel
def cuts26935 : List PrefixCut := [⟨12,45713076,45713104⟩,
⟨120,444700040,444700293⟩,
⟨128,474484195,474484464⟩]
theorem checked26935 : checkPrefixCuts (2^48) 3534356481 9 Manual.Count131072.C026935.packed 128 cuts26935 = true := by
 decide +kernel
def pointBounds26935 : List (Nat × Nat × Nat) := [(3534368768,103853084868984,103853467420223),(3534479360,103853483855948,103853866407412)]
theorem point_links_checked26935 : (cuts26935.take 2).map (fun c => (3534356481-1+2*2^9*c.k,103853039155908+c.lower,103853421707119+c.upper)) = pointBounds26935 := by
 decide +kernel
def cuts26936 : List PrefixCut := [⟨100,377233565,377233778⟩,
⟨128,480200400,480200669⟩]
theorem checked26936 : checkPrefixCuts (2^48) 3534487553 9 Manual.Count131072.C026936.packed 128 cuts26936 = true := by
 decide +kernel
def pointBounds26936 : List (Nat × Nat × Nat) := [(3534589952,103853890873668,103854273425361)]
theorem point_links_checked26936 : (cuts26936.take 1).map (fun c => (3534487553-1+2*2^9*c.k,103853513640103+c.lower,103853896191583+c.upper)) = pointBounds26936 := by
 decide +kernel
def cuts26937 : List PrefixCut := [⟨80,292252463,292252628⟩,
⟨128,470706296,470706561⟩]
theorem checked26937 : checkPrefixCuts (2^48) 3534618625 9 Manual.Count131072.C026937.packed 128 cuts26937 = true := by
 decide +kernel
def pointBounds26937 : List (Nat × Nat × Nat) := [(3534700544,103854286092966,103854668644880)]
theorem point_links_checked26937 : (cuts26937.take 1).map (fun c => (3534618625-1+2*2^9*c.k,103853993840503+c.lower,103854376392252+c.upper)) = pointBounds26937 := by
 decide +kernel
def cuts26938 : List PrefixCut := [⟨60,221371671,221371794⟩,
⟨128,475546212,475546480⟩]
theorem checked26938 : checkPrefixCuts (2^48) 3534749697 9 Manual.Count131072.C026938.packed 128 cuts26938 = true := by
 decide +kernel
def pointBounds26938 : List (Nat × Nat × Nat) := [(3534811136,103854685918470,103855068470607)]
theorem point_links_checked26938 : (cuts26938.take 1).map (fun c => (3534749697-1+2*2^9*c.k,103854464546799+c.lower,103854847098813+c.upper)) = pointBounds26938 := by
 decide +kernel
def cuts26939 : List PrefixCut := [⟨40,148027288,148027371⟩,
⟨128,471626918,471627185⟩]
theorem checked26939 : checkPrefixCuts (2^48) 3534880769 9 Manual.Count131072.C026939.packed 128 cuts26939 = true := by
 decide +kernel
def pointBounds26939 : List (Nat × Nat × Nat) := [(3534921728,103855088120299,103855470672664)]
theorem point_links_checked26939 : (cuts26939.take 1).map (fun c => (3534880769-1+2*2^9*c.k,103854940093011+c.lower,103855322645293+c.upper)) = pointBounds26939 := by
 decide +kernel
def cuts26940 : List PrefixCut := [⟨20,73891671,73891712⟩,
⟨128,473998101,473998365⟩]
theorem checked26940 : checkPrefixCuts (2^48) 3535011841 9 Manual.Count131072.C026940.packed 128 cuts26940 = true := by
 decide +kernel
def pointBounds26940 : List (Nat × Nat × Nat) := [(3535032320,103855485611600,103855868164190),(3535142912,103855885718030,103856268270843)]
theorem point_links_checked26940 : (cuts26940.take 2).map (fun c => (3535011841-1+2*2^9*c.k,103855411719929+c.lower,103855794272478+c.upper)) = pointBounds26940 := by
 decide +kernel
def cuts26941 : List PrefixCut := [⟨108,399934776,399935005⟩,
⟨128,473582540,473582807⟩]
theorem checked26941 : checkPrefixCuts (2^48) 3535142913 9 Manual.Count131072.C026941.packed 128 cuts26941 = true := by
 decide +kernel
def pointBounds26941 : List (Nat × Nat × Nat) := [(3535253504,103856285652806,103856668205848)]
theorem point_links_checked26941 : (cuts26941.take 1).map (fun c => (3535142913-1+2*2^9*c.k,103855885718030+c.lower,103856268270843+c.upper)) = pointBounds26941 := by
 decide +kernel
def cuts26942 : List PrefixCut := [⟨88,320780771,320780951⟩,
⟨128,472609407,472609676⟩]
theorem checked26942 : checkPrefixCuts (2^48) 3535273985 9 Manual.Count131072.C026942.packed 128 cuts26942 = true := by
 decide +kernel
def pointBounds26942 : List (Nat × Nat × Nat) := [(3535364096,103856680081341,103857062634601)]
theorem point_links_checked26942 : (cuts26942.take 1).map (fun c => (3535273985-1+2*2^9*c.k,103856359300570+c.lower,103856741853650+c.upper)) = pointBounds26942 := by
 decide +kernel
def cuts26943 : List PrefixCut := [⟨68,250628791,250628930⟩,
⟨128,472830781,472831044⟩]
theorem checked26943 : checkPrefixCuts (2^48) 3535405057 9 Manual.Count131072.C026943.packed 128 cuts26943 = true := by
 decide +kernel
def pointBounds26943 : List (Nat × Nat × Nat) := [(3535474688,103857082538768,103857465092256)]
theorem point_links_checked26943 : (cuts26943.take 1).map (fun c => (3535405057-1+2*2^9*c.k,103856831909977+c.lower,103857214463326+c.upper)) = pointBounds26943 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000216
